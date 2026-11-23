module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle384
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.ChamberInd

variable {m : ℕ}

def nrm (χ : Fin m → ℂˣ) : Fin m → ℝ := fun i => ‖(χ i : ℂ)‖

def wt (a : Fin m → ℝ) : ℝ := ∑ i : Fin m, ((m : ℝ) - (i.val : ℝ)) * Real.log (a i)

theorem nrm_pos (χ : Fin m → ℂˣ) (i : Fin m) : 0 < nrm χ i := by
  exact norm_pos_iff.mpr (Units.ne_zero _)

theorem wt_swap_gt (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (i j : Fin m) (hij : i.val + 1 = j.val)
    (hlt : a i < a j) : wt a < wt (a ∘ Equiv.swap i j) := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hsub : wt (a ∘ Equiv.swap i j) - wt a =
      ((m : ℝ) - (i.val : ℝ)) * (Real.log (a j) - Real.log (a i)) +
        ((m : ℝ) - (j.val : ℝ)) * (Real.log (a i) - Real.log (a j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add i j hne (fun k hk => by
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hk.1 hk.2, sub_self])]
    simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  have hj : (j.val : ℝ) = (i.val : ℝ) + 1 := by
    rw [← hij]
    push_cast
    ring
  have hlog : Real.log (a i) < Real.log (a j) := Real.log_lt_log (ha i) hlt
  have hd : wt (a ∘ Equiv.swap i j) - wt a = Real.log (a j) - Real.log (a i) := by
    rw [hsub, hj]
    ring
  linarith

theorem wt_update_gt (χ : Fin m → ℂˣ) (j : Fin m) (hj : j.val + 1 = m) (hlt : ‖(χ j : ℂ)‖ < 1) :
    wt (nrm χ) < wt (nrm (Function.update χ j (χ j)⁻¹)) := by
  have hpos : 0 < ‖(χ j : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hn : nrm (Function.update χ j (χ j)⁻¹) = Function.update (nrm χ) j (‖(χ j : ℂ)‖⁻¹) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [nrm]
    · simp [nrm, Function.update_of_ne hk]
  rw [hn]
  have hdiff : wt (Function.update (nrm χ) j ‖(χ j : ℂ)‖⁻¹) - wt (nrm χ) =
      ((m : ℝ) - (j.val : ℝ)) * (Real.log ‖(χ j : ℂ)‖⁻¹ - Real.log (nrm χ j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single j (fun k hk => by
      simp only [Function.update_of_ne hk, sub_self])]
    simp only [Function.update_self]
    ring
  have hm : (m : ℝ) - (j.val : ℝ) = 1 := by
    have hj' : (j.val : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : Real.log ‖(χ j : ℂ)‖ < 0 := Real.log_neg hpos hlt
  have e : nrm χ j = ‖(χ j : ℂ)‖ := rfl
  rw [Real.log_inv, hm, e] at hdiff
  linarith

theorem weylConj_swap {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (i j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (χ ∘ Equiv.swap i j) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨(Equiv.swap i j).trans w, fun k => hw _⟩

theorem weylConj_update {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (Function.update χ j (χ j)⁻¹) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun k => ?_⟩
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self]
    rcases hw k with h | h
    · right
      rw [h]
    · left
      rw [h, inv_inv]
  · rw [Function.update_of_ne hk]
    exact hw k

theorem finite_nrm (α : Fin m → ℂˣ) (T : Set (Fin m → ℂˣ)) (hT : ∀ β ∈ T, GlobalTheory.LGrp.WeylConjU α β) :
    (nrm '' T).Finite := by
  classical
  let S : Set ℝ := (Set.range fun k => ‖(α k : ℂ)‖) ∪ Set.range fun k => ‖(((α k)⁻¹ : ℂˣ) : ℂ)‖
  have hS : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  refine (Set.Finite.pi (t := fun _ : Fin m => S) (fun _ => hS)).subset ?_
  rintro _ ⟨β, hβ, rfl⟩
  rw [Set.mem_univ_pi]
  intro i
  obtain ⟨w, hw⟩ := hT β hβ
  rcases hw i with h | h
  · exact Or.inl ⟨w i, by simp only [nrm, h]⟩
  · exact Or.inr ⟨w i, by simp only [nrm, h]⟩

theorem exists_chamber (P : (Fin m → ℂˣ) → Prop)
    (hs : ∀ (χ : Fin m → ℂˣ) (i j : Fin m), i.val + 1 = j.val → ‖(χ i : ℂ)‖ < ‖(χ j : ℂ)‖ → P χ →
      P (χ ∘ Equiv.swap i j))
    (hv : ∀ (χ : Fin m → ℂˣ) (j : Fin m), j.val + 1 = m → ‖(χ j : ℂ)‖ < 1 → P χ →
      P (Function.update χ j (χ j)⁻¹))
    (α χ : Fin m → ℂˣ) (hα : GlobalTheory.LGrp.WeylConjU α χ) (hχ : P χ) :
    ∃ β : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ P β := by
  classical
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Fin m → ℂˣ), T = {β | GlobalTheory.LGrp.WeylConjU α β ∧ P β} := ⟨_, rfl⟩
  have hfin : (nrm '' T).Finite := finite_nrm α T (fun β hβ => by rw [hTdef] at hβ; exact hβ.1)
  have hne : (nrm '' T).Nonempty := ⟨nrm χ, χ, by rw [hTdef]; exact ⟨hα, hχ⟩, rfl⟩
  obtain ⟨_, ⟨β, hβT, rfl⟩, hmax⟩ := Set.exists_max_image (nrm '' T) wt hfin hne
  rw [hTdef] at hβT
  obtain ⟨hβα, hβP⟩ := hβT
  have hmax' : ∀ γ : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α γ → P γ → wt (nrm γ) ≤ wt (nrm β) :=
    fun γ h1 h2 => hmax _ ⟨γ, by rw [hTdef]; exact ⟨h1, h2⟩, rfl⟩
  have hadj : ∀ i j : Fin m, i.val + 1 = j.val → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    by_contra hcon
    rw [not_le] at hcon
    have h1 := hmax' _ (weylConj_swap hβα i j) (hs β i j hij hcon hβP)
    have h2 := wt_swap_gt (nrm β) (nrm_pos β) i j hij hcon
    exact absurd h1 (not_le.mpr h2)
  have key : ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro d
    induction d with
    | zero =>
      intro i j h
      rw [show j = i from Fin.ext (by omega)]
    | succ d ih =>
      intro i j h
      have hk : i.val + d < m := by
        have := j.isLt
        omega
      exact le_trans (hadj ⟨i.val + d, hk⟩ j (by show i.val + d + 1 = j.val; omega))
        (ih i ⟨i.val + d, hk⟩ rfl)
  have hmono : ∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    have h' : i.val ≤ j.val := hij
    exact key (j.val - i.val) i j (by omega)
  have hone : ∀ i, 1 ≤ ‖(β i : ℂ)‖ := by
    intro i
    have hi := i.isLt
    have hlast : (⟨m - 1, by omega⟩ : Fin m).val + 1 = m := by
      show m - 1 + 1 = m
      omega
    have hl : 1 ≤ ‖(β ⟨m - 1, by omega⟩ : ℂ)‖ := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 := hmax' _ (weylConj_update hβα _) (hv β _ hlast hcon hβP)
      have h2 := wt_update_gt β _ hlast hcon
      exact absurd h1 (not_le.mpr h2)
    exact le_trans hl (hmono i _ (by show i.val ≤ m - 1; omega))
  exact ⟨β, hβα, hmono, hone, hβP⟩

theorem chamberU : PositivityTheory.SphericalProduct.ChamberU := by
  unfold ChamberU
  intro hsw hinv
  unfold SwapStepU at hsw
  unfold InvStepU at hinv
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hadm hirr hsph α χ hα f hf hfeq
  obtain ⟨β, h1, h2, h3, hP⟩ := exists_chamber (m := n / 2)
    (fun χ => ∃ f : V →ₗ[ℂ] ↥(GlobalTheory.LFun.psSpaceU σ q χ), Function.Injective f ∧
      ∀ (g : ↥(Formalism.UG.GU σ n)) (v : V), f (ρ g v) = (GlobalTheory.LFun.psFunU σ q χ g) (f v))
    (fun χ i j hij hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hsw L ϖ σ q n hU V ρ hadm hirr hsph χ i j hij
        (by rw [norm_div, div_lt_one (norm_pos_iff.mpr (Units.ne_zero _))]; exact hlt) f hf hfeq)
    (fun χ j hj hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hinv L ϖ σ q n hU V ρ hadm hirr hsph χ j hj hlt f hf hfeq)
    α χ hα ⟨f, hf, hfeq⟩
  exact ⟨β, h1, h2, h3, hP⟩

end GlobalTheory.CompanionTheory.ChamberInd

end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.KAvg

open GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem stab_finiteIndex_of_smooth [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hc : IsCompact (K : Set G)) (ρ : Representation ℂ G V) (hs : IsSmooth ρ) (x : V) :
    (stab ρ K x).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen (stab ρ K x : Set K) :=
    (hs x).preimage continuous_subtype_val
  haveI : Finite (K ⧸ stab ρ K x) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

private theorem normalCore_stab_le_stab_apply (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) (k : K) :
    (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := by
  intro n hn
  have hc : k⁻¹ * n * k ∈ stab ρ K x := by
    have h1 := (Subgroup.normalCore_normal (stab ρ K x)).conj_mem n hn k⁻¹
    rw [inv_inv] at h1
    exact Subgroup.normalCore_le _ h1
  rw [mem_stab] at hc ⊢
  have he : (n : G) * (k : G) = (k : G) * ((k⁻¹ * n * k : K) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc ρ (n : G) (ρ (k : G) x) = ρ ((n : G) * (k : G)) x := by
        rw [map_mul, Module.End.mul_apply]
    _ = ρ (k : G) (ρ ((k⁻¹ * n * k : K) : G) x) := by
        rw [he, map_mul, Module.End.mul_apply]
    _ = ρ (k : G) x := by rw [hc]

theorem avg_translate (ρ : Representation ℂ G V) (K : Subgroup G) {x : V}
    (hx : (stab ρ K x).FiniteIndex) (k : K) : avg ρ K (ρ (k : G) x) = avg ρ K x := by
  haveI := hx
  have hN1 : (stab ρ K x).normalCore ≤ stab ρ K x := Subgroup.normalCore_le _
  have hN2 : (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := normalCore_stab_le_stab_apply ρ K x k
  rw [avg_eq ρ K hN2, avg_eq ρ K hN1]
  unfold avgH
  congr 1
  have key : ∀ q : K ⧸ (stab ρ K x).normalCore,
      cv ρ K (stab ρ K x).normalCore (ρ (k : G) x) q =
        cv ρ K (stab ρ K x).normalCore x (q * (QuotientGroup.mk k)) := by
    intro q
    have hq : q * (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore) = QuotientGroup.mk (q.out * k) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq, cv_mk ρ K hN1]
    simp only [cv, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [key]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore))

end GlobalTheory.CompanionTheory.KAvg


open GlobalTheory.OrbitAvg GlobalTheory.CompanionTheory.KAvg in
theorem GlobalTheory.CompanionTheory.KAvg.kInvForm : PositivityTheory.SphericalProduct.KInvForm := by
  unfold PositivityTheory.SphericalProduct.KInvForm
  intro G _ _ _ K _ hc V _ _ ρ hs v₀ hv₀ hne
  have hfi : ∀ x : V, (stab ρ K x).FiniteIndex := fun x => stab_finiteIndex_of_smooth K hc ρ hs x
  let A : V →ₗ[ℂ] V :=
    { toFun := fun x => avg ρ K x
      map_add' := fun x y => avg_add ρ K (hfi x) (hfi y)
      map_smul' := fun c x => avg_smul ρ K (hfi x) c }
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp h)
  have hfix : ∀ l ∈ K, ρ l v₀ = v₀ := by
    intro l hl
    have h' : ∀ h : K, ρ h v₀ = ((1 : K →* ℂˣ) h : ℂ) • v₀ := hv₀
    simpa using h' ⟨l, hl⟩
  refine ⟨((f v₀)⁻¹ • f) ∘ₗ A, ?_, ?_⟩
  · intro k hk
    ext v
    show ((f v₀)⁻¹ • f) (avg ρ K (ρ k v)) = ((f v₀)⁻¹ • f) (avg ρ K v)
    rw [avg_translate ρ K (hfi v) ⟨k, hk⟩]
  · show ((f v₀)⁻¹ • f) (avg ρ K v₀) = 1
    rw [avg_fixed ρ K (hfi v₀) hfix, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.KUFactsU

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem iwGL_entries {n : ℕ} {x : GL (Fin n) L} (hx : x ∈ IwGL L n) (i j : Fin n) :
    (x : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  have hk := (Subgroup.mem_iInf.1 hx) (Fin.last n)
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  have hmem : (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    intro l
    simp only [Fin.val_last, l.isLt, if_true]
    by_cases hl : l = j
    · subst hl
      simp
    · simp [Pi.single_apply, hl]
  have h2 : (Matrix.GeneralLinearGroup.toLin : GL (Fin n) L ≃* _).toMonoidHom x •
      (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    rw [← hk]
    exact Set.smul_mem_smul_set hmem
  have h3 := h2 i
  simp only [Fin.val_last, i.isLt, if_true] at h3
  show (x : Matrix (Fin n) (Fin n) L) i j ∈ Valued.v.integer
  rw [Valuation.mem_integer_iff]
  convert h3 using 2
  simp [Units.smul_def, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem iwU_le_KU (σ : L →+* L) (n : ℕ) : IwU σ n ≤ KU σ n := by
  intro x hx
  have hx' : (x : GL (Fin n) L) ∈ IwGL L n := Subgroup.mem_subgroupOf.1 hx
  have hxi : ((x : GL (Fin n) L))⁻¹ ∈ IwGL L n := inv_mem hx'
  have hmem : x ∈ ((KU σ n : Subgroup (GU σ n)) : Set (GU σ n)) := by
    rw [GlobalTheory.LFun.IntPtsUnitary.coe_KU, Set.mem_preimage, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    exact ⟨fun i j => iwGL_entries hx' i j, fun i j => iwGL_entries hxi i j⟩
  exact hmem

theorem ordL_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (d : ℤ) : ordL (ϖ ^ d) = d := by
  have h1 : Valued.v (ϖ ^ d) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_neg, smul_eq_mul, mul_one]
  have hne : Valued.v (ϖ ^ d) ≠ 0 := by
    rw [h1]
    exact WithZero.coe_ne_zero
  unfold ordL
  rw [dite_eq_right hne]
  have key : WithZero.unzero hne = Multiplicative.ofAdd (-d) :=
    WithZero.coe_injective (by rw [WithZero.coe_unzero, h1])
  rw [key, toAdd_ofAdd, neg_neg]

def expo (n : ℕ) (i : Fin n) : ℤ := (n : ℤ) - 1 - 2 * (i.val : ℤ)

def tGL {ϖ : L} (h0 : ϖ ≠ 0) (n : ℕ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ expo n i
  inv := Matrix.diagonal fun i => ϖ ^ (-expo n i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp

theorem tGL_mem {ϖ : L} (h0 : ϖ ≠ 0) {σ : L →+* L} (hσ : σ ϖ = ϖ) (n : ℕ) : tGL h0 n ∈ GU σ n := by
  show cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
    ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n
  have hc : cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ϖ ^ expo n i := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT, tGL, map_zpow₀, hσ]
    · simp [cT, tGL, hab, Ne.symm hab]
  rw [hc]
  ext a b
  simp only [tGL, Matrix.diagonal_mul, Matrix.mul_diagonal, antiJ]
  split_ifs with hab
  · have he : expo n a + expo n b = 0 := by
      unfold expo
      omega
    rw [mul_one, ← zpow_add₀ h0, he, zpow_zero]
  · simp

theorem exists_strictDom {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ t : GU σ n, IsDiagM (t : GL (Fin n) L) ∧ IsStrictDom (t : GL (Fin n) L) := by
  obtain ⟨-, -, hσ, hϖ, -⟩ := h
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨⟨tGL h0 n, tGL_mem h0 hσ n⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · show (Matrix.diagonal fun i => ϖ ^ expo n i) i j = 0
    exact Matrix.diagonal_apply_ne _ hij
  · show ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) j j) <
      ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) i i)
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ordL_zpow hϖ, ordL_zpow hϖ]
    unfold expo
    have hlt : (i : ℕ) < j := hij
    omega

theorem kuFacts : PositivityTheory.SphericalProduct.KUFacts := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  exact ⟨ho, hc, iwU_le_KU σ n, exists_strictDom h n⟩

end GlobalTheory.CompanionTheory.KUFactsU

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.WeilM Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

namespace GlobalTheory.CompanionTheory.ThetaCoord

variable {F : Type} [Field F] [NumberField F] {κ : Type}



def finOf (a : κ → AF F) : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2

def infOf (a : κ → AF F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

end GlobalTheory.CompanionTheory.ThetaCoord

end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.linear_recurrence_growth_bound : ∀ (D : ℕ) (κ' κ : ℝ), κ' < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
  (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ),
  (∀ i, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) = 0) → (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
  ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  first | exact @GlobalTheory.CompanionTheory.LinRec.uniformRecBound | exact GlobalTheory.CompanionTheory.LinRec.uniformRecBound | (intros; apply GlobalTheory.CompanionTheory.LinRec.uniformRecBound <;> assumption)
end
