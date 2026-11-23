module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.HermitianCurvature.StatementNF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.StartForm

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

end GlobalTheory.HatNF.StartForm

namespace GlobalTheory.HatNF

open StartForm

open MeasureTheory in
private lemma prod_ofFn_mul_prod_ofFn_eq_one {A : Type} [Ring A] :
    ∀ {n : ℕ} (f g : Fin n → A), (∀ i, f i * g i = 1) → (∀ i j, Commute (f i) (g j)) →
      (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hrest : (List.ofFn fun i : Fin n => f i.succ).prod *
        (List.ofFn fun i : Fin n => g i.succ).prod = 1 :=
      prod_ofFn_mul_prod_ofFn_eq_one _ _ (fun i => h i.succ) (fun i j => hc i.succ j.succ)
    have hcomm : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) :=
      Commute.list_prod_left _ _ (List.forall_mem_ofFn_iff.mpr fun i => hc i.succ 0)
    simp only [mul_assoc]
    rw [hcomm.left_comm, ← mul_assoc (f 0), h 0, hrest, one_mul]

open MeasureTheory in
private lemma levelConstants_commute {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r)
    {x y : A}
    (hx : x ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi})
    (hy : y ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}) : Commute x y :=
  L.fns_comm x hx y hy

open MeasureTheory in
private lemma commute_prod_ofFn {A : Type} [Ring A] {n : ℕ} (a : A) (f : Fin n → A)
    (h : ∀ i, Commute a (f i)) : Commute a (List.ofFn f).prod :=
  Commute.list_prod_right _ _ (List.forall_mem_ofFn_iff.mpr h)

open MeasureTheory in
theorem _root_.GlobalTheory.HatNF.start_normalForm : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A), _root_.GlobalTheory.HatNF.HatHyp d → ∀ (L : _root_.Formalism.FourierDecayAlt.R.LevelData A P.r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) (s : ℂ), _root_.GlobalTheory.HatNF.Comparison₂ d L st s → (∀ x ∈ _root_.Formalism.FourierDecayAlt.TL.kAlg st, x ∈ Set.range d.κ) ∧ ∀ Y ∈ st.inv, ∃ E ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0, L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y = d.L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * E := by
  intro P A _ _ _ _ d hHyp L st s hTie
  obtain ⟨hA, hSame, hs, hQ, hinv⟩ := hTie
  obtain ⟨-, -, hRel, -⟩ := hHyp
  obtain ⟨-, hκfns, -⟩ := hRel
  obtain ⟨-, -, -, -, -, -, -, hζi, hζb, -, hGG, hGGi, -⟩ := hSame
  have hst := hA.start
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num

  have hκ : ∀ (f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ) (g : A), g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) →
      Commute (d.κ f) g := by
    intro f g hg
    exact hκfns f g (Or.inl (by unfold _root_.Formalism.FourierDecayAlt.R.LevelData.fns; exact Or.inr hg))

  have hx : ∀ Y, st.x Y = s • d.x Y := by
    intro Y
    have h11 := congrFun (congrFun (hQ Y) 1) 1
    rw [hst.tau Y, hGG] at h11
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h11
    simp at h11
    calc st.x Y = d.L.GGi * (d.L.GG * st.x Y) := by rw [← mul_assoc, d.L.GGi_GG, one_mul]
      _ = s • d.x Y := by rw [h11, mul_smul_comm, ← mul_assoc, d.L.GGi_GG, one_mul]

  have hxinv : ∀ Y ∈ st.inv, d.x Y * d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) = 1 ∧
      d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.x Y = 1 := by
    intro Y hY
    rw [hinv] at hY
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
    rw [← map_mul, ← map_mul, ← map_one d.κ]
    constructor
    · congr 1; funext ρ; exact mul_inv_cancel₀ (hY ρ)
    · congr 1; funext ρ; exact inv_mul_cancel₀ (hY ρ)
  refine ⟨?_, ?_⟩
  · intro a ha
    have hle : _root_.Formalism.FourierDecayAlt.TL.kAlg st ≤ d.κ.range := by
      unfold _root_.Formalism.FourierDecayAlt.TL.kAlg
      refine Algebra.adjoin_le ?_
      rintro b (⟨Y, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · rw [hx Y]
        unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
        exact ⟨s • fun ρ => _root_.Formalism.FourierDecayAlt.M.xC P ρ Y, by simp [map_smul]⟩
      · have hxi : st.xi Y = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
          have hright : st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) = 1 := by
            rw [hx Y, smul_mul_smul_comm, mul_inv_cancel₀ hs0, (hxinv Y hY).1, one_smul]
          calc st.xi Y = st.xi Y * (st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹))) := by
                rw [hright, mul_one]
            _ = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
                rw [← mul_assoc, (hst.x_xi Y hY).2, one_mul]
        rw [hxi]
        exact ⟨s⁻¹ • fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹, by simp [map_smul]⟩
    rw [← AlgHom.coe_range]
    exact hle ha
  · intro Y hY
    obtain ⟨hXXi, hXiX⟩ := hxinv Y hY
    have h10 := congrFun (congrFun (hQ Y) 1) 0
    rw [hst.low Y hY, hx Y, hGG, hζb, hζi, hGGi] at h10
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h10
    simp at h10
    rw [← smul_add] at h10
    have h10' : d.L.GG * d.x Y * (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y) =
        d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := by
      have h := congrArg (fun a => s⁻¹ • a) h10
      simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul] using h
    have hcancel : ∀ a : A, d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * a)) = a := by
      intro a
      simp only [← mul_assoc]
      rw [mul_assoc _ d.L.GGi d.L.GG, d.L.GGi_GG, mul_one, hXiX, one_mul]
    have key : L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y =
        d.L.l0 Y + d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * d.weightedSumBis Y) := by
      have h : d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y *
          (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y)) := by
        rw [h10']
      rw [hcancel, mul_add, mul_add, hcancel] at h
      exact h
    have hmem : ∀ b ∈ _root_.GlobalTheory.HatNF.bmon d, b ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0 := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.nfSpan
      exact Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩
    have hgen : ∀ b ∈ _root_.GlobalTheory.HatNF.bset d, b ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.bmon
      exact Submonoid.subset_closure hb
    have hκgen : ∀ f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ, d.κ f ∈ _root_.GlobalTheory.HatNF.bmon d := fun f =>
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))
    have hDgen : d.L.D * d.L.Dbi ∈ _root_.GlobalTheory.HatNF.bmon d :=
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inl (by simp))))
    have hPgen : ∀ l ∈ Finset.Icc 1 (P.k - 1), d.L.Drb * d.L.Dri * d.SS l ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro l hl
      refine hgen _ ?_
      unfold _root_.GlobalTheory.HatNF.bset
      refine Or.inl (Or.inr ⟨l, by simpa using hl, ?_⟩)
      unfold _root_.GlobalTheory.HatNF.ssn
      rfl
    have hDD : ∀ l, d.L.D * d.L.Dbi * (d.L.Drb * d.L.Dri * d.SS l) = d.L.ζ * (d.L.ζbi * d.SS l) := by
      intro l
      have hcb : (List.ofFn d.L.cbi).prod * (List.ofFn d.L.cb).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.cbi_cb
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hc : (List.ofFn d.L.c).prod * (List.ofFn d.L.ci).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.c_ci
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hζci : Commute d.L.ζ (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      have hζbici : Commute d.L.ζbi (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.D _root_.Formalism.FourierDecayAlt.R.LevelData.Dbi _root_.Formalism.FourierDecayAlt.R.LevelData.Drb _root_.Formalism.FourierDecayAlt.R.LevelData.Dri _root_.Formalism.FourierDecayAlt.R.LevelData.Dr _root_.Formalism.FourierDecayAlt.R.LevelData.Drbi
      simp only [mul_assoc]
      rw [← mul_assoc (List.ofFn d.L.cbi).prod, hcb, one_mul, ← hζbici.symm.left_comm,
        ← hζci.symm.left_comm, ← mul_assoc, hc, one_mul]
    have hGGiζ : Commute d.L.GGi d.L.ζ := levelConstants_commute d.L (by simp) (by simp)
    have hGGiζbi : Commute d.L.GGi d.L.ζbi := levelConstants_commute d.L (by simp) (by simp)
    have hXiζ : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζ := hκ _ _ (by simp)
    have hXiζbi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζbi := hκ _ _ (by simp)
    have hXiGGi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.GGi := hκ _ _ (by simp)
    refine ⟨d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.weightedSumBis Y)), ?_, ?_⟩
    · have hS : d.weightedSumBis Y = ∑ l ∈ Finset.Icc 1 (P.k - 1), d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := rfl
      rw [hS, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Submodule.sum_mem _ (fun l hl => hmem _ ?_)
      have heq : d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) *
          (d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y)))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.D * d.L.Dbi) * (d.L.Drb * d.L.Dri * d.SS l) *
            d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := by
        rw [mul_assoc (d.κ _) (d.L.D * d.L.Dbi), hDD, ← hXiζbi.left_comm, ← hXiζ.left_comm]
        simp only [mul_assoc]
      rw [heq]
      exact mul_mem (mul_mem (mul_mem (hκgen _) hDgen) (hPgen l hl)) (hκgen _)
    · rw [hζb, hζi, hGGi, key]
      congr 1
      simp only [mul_assoc]
      rw [hGGiζ.left_comm, hGGiζbi.left_comm, ← mul_assoc d.L.ζi, d.L.ζi_ζ, one_mul,
        ← mul_assoc d.L.ζb, d.L.ζb_ζbi, one_mul, hXiGGi.left_comm]

end GlobalTheory.HatNF
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RaiseFormula

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem up_unique {j : ℕ} {a b c : M.Ty P} (h : M.Up P j a b) (h' : M.Up P j a c) : b = c := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem up_index {l j : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b)
    (h' : M.Up P j a b) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 := h' ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1 h2
  by_contra hne
  rw [if_neg (fun x => hne x.symm)] at h2
  omega

theorem up_ne {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b) : b ≠ a := by
  rw [Finset.mem_Icc] at hl
  rintro rfl
  have h1 := h ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1
  omega

omit [StarRing A] in
theorem sum_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : ∑ ρ, NF.proj κ ρ = 1 := by
  unfold NF.proj

  rw [← map_sum, ← map_one κ]
  congr 1
  funext x
  simp [Finset.sum_apply]

omit [StarRing A] in
theorem kap_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (f : M.Ty P → ℂ) (ρ : M.Ty P) :
    κ f * NF.proj κ ρ = f ρ • NF.proj κ ρ := by
  unfold NF.proj
  rw [← map_mul, ← map_smul]
  congr 1
  funext x
  by_cases h : x = ρ <;> simp [h]

omit [StarRing A] in
theorem proj_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) {ρ ρ' : M.Ty P} (h : ρ' ≠ ρ) :
    NF.proj κ ρ' * NF.proj κ ρ = 0 := by
  have := kap_mul_proj κ (fun x => if x = ρ' then 1 else 0) ρ
  rw [if_neg (Ne.symm h), zero_smul] at this
  exact this

theorem proj_SS_proj (d : Q.NFData P A) (hd : d.Rel) {j : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P j ρ ρ') :
    NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ = 0 := by
  have h1 := hd.2.2.2.1 j (fun a => if M.Up P j a ρ' then 1 else 0) (fun x => if x = ρ' then 1 else 0) (by
    intro a b hab
    by_cases hb : b = ρ'
    · subst hb; simp [hab]
    · have : ¬ M.Up P j a ρ' := fun h' => hb (up_unique hab h')
      simp [hb, this])
  have h2 : NF.proj d.κ ρ' * d.SS j = _ := h1
  rw [h2, mul_assoc, kap_mul_proj, if_neg h, zero_smul, mul_zero]

theorem proj_raising_proj_eq_smul (d : Q.NFData P A) (hd : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ)
    {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ =
      M.xEx P {l} ρ Y • (NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ) := by
  have hq : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have hc : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (NF.proj d.κ ρ') g := fun g hg => hd.2.1 _ g hg
  have c1 : Commute (NF.proj d.κ ρ') d.L.GG := hc _ (by simp [LevelData.fns])
  have c2 : Commute (NF.proj d.κ ρ') d.L.GGi := hc _ (by simp [LevelData.fns])
  have c3 : Commute (NF.proj d.κ ρ') d.L.ζb := hc _ (by simp [LevelData.fns])
  have c4 : Commute (NF.proj d.κ ρ') d.L.nab := hc _ (by simp)
  have c5 : Commute (NF.proj d.κ ρ') (d.x Y) := by
    unfold NF.proj Q.NFData.x
    exact (Commute.all _ _).map d.κ
  have c6 : Commute (NF.proj d.κ ρ') (d.L.l0 Y) := by
    unfold LevelData.l0
    exact c4.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right (c3.mul_right c2))
  have c7 := (c1.mul_right c5).mul_right c6
  rw [hq, mul_add, add_mul, c7.eq, mul_assoc _ (NF.proj d.κ ρ'), proj_mul_proj _ (up_ne hl h), mul_zero, zero_add]
  unfold Q.NFData.weightedSumBis
  have key : ∀ j, NF.proj d.κ ρ' * (d.SS j * d.κ fun ρ => M.xEx P {j} ρ Y) * NF.proj d.κ ρ =
      M.xEx P {j} ρ Y • (NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (d.κ _), kap_mul_proj, mul_smul_comm]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
  · exact key l
  · intro j _ hj
    rw [key, proj_SS_proj d hd (fun h' => hj (up_index hl h h')), smul_zero]
  · intro h'; exact absurd hl h'

theorem xEx_ne_zero (ex : Finset ℕ) (ρ : M.Ty P) (Y : ℂ) (h : M.xC P ρ Y ≠ 0) : M.xEx P ex ρ Y ≠ 0 := by
  unfold M.xC at h
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff] at h ⊢
  exact fun i hi => h i (Finset.mem_sdiff.1 hi).1

theorem ss_formula : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Y : ℂ, (∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0) → ∃ co : M.Ty P → M.Ty P → ℂ, d.SS l = ∑ ρ, ∑ ρ', co ρ ρ' • (NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ) := by
  intro P A _ _ _ _ d hd l hl Y hY
  have hr : d.Rel := hd.2.2.1
  refine ⟨fun ρ ρ' => if M.Up P l ρ ρ' then (M.xEx P {l} ρ Y)⁻¹ else 0, ?_⟩
  have h0 : d.SS l = ∑ ρ, ∑ ρ', NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_proj, one_mul, mul_one]
  refine h0.trans (Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_)
  by_cases h : M.Up P l ρ ρ'
  · simp only [if_pos h]
    rw [proj_raising_proj_eq_smul d hr hl Y h, smul_smul, inv_mul_cancel₀ (xEx_ne_zero _ _ _ (hY ρ)), one_smul]
  · simp only [if_neg h]
    rw [zero_smul, proj_SS_proj d hr h]

end GlobalTheory.HatNF.RaiseFormula
end

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ContDiff

theorem mulT_ld_contDiff {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv q hφ

theorem mulT_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have : (fun w : ℂ => Complex.normSq w) = fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
    funext w; simp [Complex.normSq_apply]
  rw [this]
  fun_prop

theorem mulT_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ContDiffOn ℝ ∞ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ))
      {w : ℂ | T < Complex.normSq w} := by
  have h1 : ContDiffOn ℝ ∞ (fun w : ℂ => Real.log (a * (Complex.normSq w - T)))
      {w : ℂ | T < Complex.normSq w} := by
    refine ContDiffOn.log (contDiff_const.mul (mulT_normSq_contDiff.sub contDiff_const)).contDiffOn ?_
    intro w hw
    exact (mul_pos ha (sub_pos.2 hw)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((mulT_ld_contDiff hφ q).comp_contDiffOn h1)

theorem mulT_fderiv {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) (v : ℂ) :
    fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w v =
      ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) * (Complex.normSq w - T)⁻¹ *
        (2 * (w.re * v.re + w.im * v.im)) : ℝ) : ℂ) := by
  have hp : 0 < Complex.normSq w - T := sub_pos.2 hw
  have hn : HasFDerivAt (fun w : ℂ => Complex.normSq w)
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
    have : (fun w : ℂ => Complex.normSq w) =
        fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
      funext w; simp [Complex.normSq_apply]
    rw [this]
    have h1 := Complex.reCLM.hasFDerivAt (x := w)
    have h2 := Complex.imCLM.hasFDerivAt (x := w)
    refine ((h1.mul h1).add (h2.mul h2)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
    ring
  have h1 := ((hn.sub_const T).const_mul a).log (mul_pos ha hp).ne'
  have h2 : HasDerivAt (iteratedDeriv q (fun u : ℝ => φ (Real.exp u)))
      (LE.ld (q + 1) φ (a * (Complex.normSq w - T))) (Real.log (a * (Complex.normSq w - T))) := by
    unfold LE.ld
    rw [iteratedDeriv_succ]
    exact (((mulT_ld_contDiff hφ q).differentiable (by simp)) _).hasDerivAt
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp_hasFDerivAt w h1)
  have h4 : fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w = _ := h3.fderiv
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_apply,
    add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  congr 1
  field_simp

theorem mulT_dZ {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) :
    NF.dZ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      star w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) ∧
    NF.dZb (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) := by
  unfold NF.dZ NF.dZb
  rw [mulT_fderiv hφ q ha T hw, mulT_fderiv hφ q ha T hw, ← Complex.ofReal_inv]
  generalize LE.ld (q + 1) φ (a * (Complex.normSq w - T)) = b
  generalize (Complex.normSq w - T)⁻¹ = e
  constructor <;> apply Complex.ext <;> simp <;> ring


open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx4 in
theorem t_mul_mulG (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hφ : LE.SmoothLog φ)
    (hW : IsMulG P Bs φ W) (q : ℕ) (Y : ℂ) :
    X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧
      X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧
      X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  have hU := isOpen_normSq_gt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')
  have hDU := Dp_maps (k := P.k) (r := P.r) Bs.z Bs.z'
  have hD := Qx5.Dp_open P.k P.r Bs.z Bs.z'
  have ha : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < Complex.normSq (∏ a, x.1 a) := fun x hx =>
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)
  have key := fun (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r)
      (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    zeta_smooth_level Bs.z Bs.z' hD hU hDU (mulT_contDiffOn hφ q (ha x hx) _) (Qx5.slice_smooth Φ.2 hx.1)
      ⟨hx.2.1, hx.2.2⟩ Y
  have hd := fun (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    mulT_dZ hφ q (ha x hx) _ (hDU x.2 hx.2.2)
  have hWa : ∀ (p : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      (W p Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        ((LE.ld p φ (Complex.normSq (∏ a, c a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) -
          Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g :=
    fun p Φ c g => hW p Φ c g
  have ht : ∀ (a b : Fin 2) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r),
      x ∈ Q.DomR P.k P.r Bs.z Bs.z' → (X.t Y a b (W q Φ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (fun y =>
          ((LE.ld q φ (Complex.normSq (∏ a, x.1 a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) y) -
            Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y) x.2 := by
    intro a b Φ x hx
    rw [X.t_apply Y a b _ x hx]
    congr 1
    funext y
    exact hWa q Φ x.1 y
  refine ⟨end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_⟩
  · rw [Module.End.mul_apply, ht 1 0 Φ x hx, (key Φ x hx).1, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
      Pi.sub_apply, X.fn_apply 2 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 1 0 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).1, smul_smul, smul_smul, mul_assoc]
    rfl
  · rw [Module.End.mul_apply, ht 1 1 Φ x hx, (key Φ x hx).2.1, Module.End.mul_apply, hWa,
      X.t_apply Y 1 1 Φ x hx]
  · rw [Module.End.mul_apply, ht 0 1 Φ x hx, (key Φ x hx).2.2, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, X.fn_apply 0 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 0 1 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).2, smul_smul, smul_smul, mul_assoc]
    rfl

theorem nf_t_mul_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 :=
  fun Wp Wq _ _ _ _ _ _ P Bs X _ _ _ _ _ _ _ φ W hφ hW q Y => t_mul_mulG Wp Wq P Bs X φ W hφ hW q Y

end GlobalTheory.HatNF
end
