module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle433
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacEquiv

theorem acts_schr_of_ref {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    (w : (κ → AF F) × (κ → AF F)) (h₁ : At (evFin F v) w.1) (h₂ : At (evFin F v) w.2)
    (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0) (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x)
    (φ φ₁ : (κ → Fv F v) → ℂ) (h : schr ψ w (tens (evFin F v) φ R) = tens (evFin F v) φ₁ R) :
    Acts (evFin F v) (schr ψ w) φ φ₁ := by
  intro r hr
  funext x
  set y : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (x i)) with hyD
  have hev : ∀ i, evFin F v (y i) = evFin F v (x i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have hy : At (evFin F v) y := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hRy : R y = R 0 := by simpa using hR 0 y hy
  have hRyw : R (y + w.1) = R y := hR y w.1 h₁
  have hrx : r (x + w.1) = r x := hr.1 x w.1 h₁
  have hdot : x ⬝ᵥ w.2 = y ⬝ᵥ w.2 := by
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : evFin F v (x i - y i) = 0 := by rw [map_sub, hev, sub_self]
    have h0 := congrFun (h₂ (x i - y i) hz) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    rw [← sub_eq_zero, ← sub_mul, h0]
  have hφ : (fun i => evFin F v ((x + w.1) i)) = (fun i => evFin F v ((y + w.1) i)) := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), hev]
  have hφ₁ : (fun i => evFin F v (x i)) = (fun i => evFin F v (y i)) := by
    funext i
    exact (hev i).symm
  have key := congrFun h y
  simp only [schr, tens] at key ⊢
  rw [hRyw, hRy] at key
  rw [hdot, hrx, hφ₁]
  have hcanc : ψ (y ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * φ (fun i => evFin F v ((x + w.1) i)) =
      φ₁ (fun i => evFin F v (y i)) := by
    apply mul_right_cancel₀ hR0
    rw [hφ, ← key, mul_assoc]
  rw [← mul_assoc, hcanc]

theorem heisInv_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v m C l hl g _ S hS u hu φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hRest⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hsp := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  set u' := GlobalTheory.WeilM.actAB (cA σ) ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u with hu'D
  have hu'eq : u' = mat g * u := by
    simp [hu'D, GlobalTheory.WeilM.actAB, mat]
  obtain ⟨huAt, z, hz⟩ := hu
  have hAt' : At (evFin F v) u' := by
    intro c hc
    rw [hu'eq, ← Matrix.mul_smul, huAt c hc, Matrix.mul_zero]
  have hlag : u' ∈ GlobalTheory.InertVacLag.lagAt v C := ⟨hAt', mat g * z, by rw [hu'eq, hz, Matrix.mul_assoc]⟩
  have hco1 : At (evFin F v) (G.M'.co.e u').1 := by
    intro c hc
    rw [← Prod.smul_fst, ← map_smul, hAt' c hc, map_zero, Prod.fst_zero]
  have hco2 : At (evFin F v) (G.M'.co.e u').2 := by
    intro c hc
    rw [← Prod.smul_snd, ← map_smul, hAt' c hc, map_zero, Prod.snd_zero]
  have hRinv := (hRest 0 (Submodule.zero_mem _)).1
  have hact : Acts (evFin F v) (G.M'.co.rho B.ψ u') (S φ) (S φ₁) := by
    apply acts_schr_of_ref v B.ψ (G.M'.co.e u') hco1 hco2 R hR0 hRinv
    have e1 := (hS φ hφ).2 R (hRest φ hφ)
    have e2 := (hS φ₁ hφ₁).2 R (hRest φ₁ hφ₁)
    have e3 := hA R (hRest φ hφ)
    have e4 := hsp.impl ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u (tens (evFin F v) φ R) (hRest φ hφ).2
    show G.M'.co.rho B.ψ u' (tens (evFin F v) (S φ) R) = tens (evFin F v) (S φ₁) R
    rw [← e1, ← e2, ← e3, hu'D]
    exact e4.symm
  exact hl u' hlag (S φ) (hS φ hφ).1 (S φ₁) (hS φ₁ hφ₁).1 hact

end GlobalTheory.InertVacEquiv
end
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

namespace GlobalTheory.EvOnto


open scoped Classical in
theorem ev_surjOn_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) →
    ∀ v, ∀ χ ∈ SB (κ → Fv F v), ∃ ψ ∈ SB (κ → Fv F v), ev v ψ = χ := by
  intro F _ _ κ _ e ei ev hSBev hfix he hsurj hne v χ hχ
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let Φ₁ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ := fun w => ev w (stdInd F κ w)
  have hstdSB : ∀ w : Pl (F := F), stdInd F κ w ∈ SB (κ → Fv F w) := fun w => GlobalTheory.StdVacuum.indicator_mem_SB w
  have hΦstd : ∀ᶠ w in cofinite, Φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := hfix
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) ∈ schA F κ := by
    refine GlobalTheory.TensUniq.pure_mem_schA f₀ _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually Φ₁ v χ hΦstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hSBev w _ (hstdSB w)
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj hmem
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ w in cofinite, φ i w = stdInd F κ w := by
    intro i
    filter_upwards [T.eventually_cofinite_notMem] with w hT
    exact hstd i w hT
  have hvac' : ∀ i, ∀ᶠ w in cofinite, (fun w => ev w (φ i w)) w =
      Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hvac i, hfix] with w h1 h2
    rw [h1]; exact h2
  have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) =
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by

    rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f₀ Φ₁ hΦstd
  choose r hr hrt using fun i => GlobalTheory.PureFactor.exists_rest_factor v (ei (f i)) (fun w => ev w (φ i w)) (hvac' i)
  have hrt' : ∀ i, tens (evFin F v) (ev v (φ i v)) (r i) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by
    intro i
    rw [hrt i]
    congr 1
    exact Function.update_eq_self v (fun w => ev w (φ i w))
  have hex : ∃ x₀, r₀ x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v fun _ => 1) = 0 := by
      rw [← hr₀t]
      funext x
      simp [tens, hc]
    have hf : f₀ = 0 := by
      refine GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ _ (fun w => ?_)
        (GlobalTheory.PureFactor.update_eventually Φ₁ v _ hΦstd) h0
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        intro h
        exact one_ne_zero (congrFun h 0)
      · rw [Function.update_of_ne hw]; exact hne w
    exact hf₀ (by rw [hf]; rfl)
  obtain ⟨x₀, hx₀⟩ := hex
  refine ⟨∑ i, (r i x₀ / r₀ x₀) • φ i v, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hSB i v), ?_⟩
  funext y
  let z : κ → AF F := fun j => GlobalTheory.LatVac.liftV v (y j - evFin F v (x₀ j))
  have hz : At (evFin F v) z := by
    intro u hu
    funext j
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun j => evFin F v ((x₀ + z) j)) = y := by
    funext j
    rw [Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV]
    ring
  have key : χ y * r₀ x₀ = ∑ i, ev v (φ i v) y * r i x₀ := by
    have h := congrFun hid (x₀ + z)
    rw [← hr₀t, Finset.sum_apply] at h
    simp only [← hrt', tens, hev, hr₀ x₀ z hz] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [hr i x₀ z hz]

  rw [map_sum, Finset.sum_apply]
  apply mul_right_cancel₀ hx₀
  rw [key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.EvOnto
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.ArchBij

theorem bijective_arch : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) → Function.Bijective ei := by
  intro F _ _ κ _ e ei ev hSB hfix he hbij hne
  have hstdSB : ∀ v, stdInd F κ v ∈ SB (κ → Fv F v) := fun v => GlobalTheory.StdVacuum.indicator_mem_SB v
  have hstd0 : ∀ v, stdInd F κ v ≠ 0 := by
    intro v h0
    have h := congrFun h0 0
    have hm : (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem (v.adicCompletionIntegers F)
    simp only [stdInd, Set.indicator_of_mem hm, Pi.one_apply, Pi.zero_apply] at h
    exact one_ne_zero h
  constructor
  · refine (injective_iff_map_eq_zero ei).2 fun f hf => ?_
    have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) ∈ schA F κ :=
      GlobalTheory.TensUniq.pure_mem_schA f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl)
    have h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ)) = e 0 := by
      rw [he f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) = 0 :=
      hbij.injOn hmem (schA F κ).zero_mem h1
    exact GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f (stdInd F κ) hstd0 (Filter.Eventually.of_forall fun _ => rfl) h2
  · intro h
    let Φ₁ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ := fun w => ev w (stdInd F κ w)
    have hΦ₁SB : ∀ v, Φ₁ v ∈ SB (κ → Fv F v) := fun v => hSB v _ (hstdSB v)
    have hΦ₁std : ∀ᶠ v in Filter.cofinite,
        Φ₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := hfix
    have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA h Φ₁ hΦ₁SB hΦ₁std
    obtain ⟨Ψ, hΨ, heΨ⟩ := hbij.surjOn h₁
    obtain ⟨T, m, f, φ, hφSB, hφstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F κ Ψ hΨ
    have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = stdInd F κ v := fun i =>
      T.eventually_cofinite_notMem.mono fun v hT => hφstd i v hT
    have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun v => ev v (φ i v) := by

      rw [← heΨ, hsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hφSB i) (hvac i)
    obtain ⟨y, hy⟩ := GlobalTheory.ArchSurj.exists_point_ne_zero Φ₁ hne hΦ₁std
    set c : ℂ := ∏ᶠ v, Φ₁ v (fun j => y j v) with hc
    have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
    set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
    refine ⟨∑ i, (cs i / c) • f i, ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    let a : κ → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
    have hI : (fun j => evI F (a j)) = x := by
      funext j
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
    have hx : h x * c = ∑ i, ei (f i) x * cs i := by
      have := congrFun hid a
      rw [Finset.sum_apply] at this
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
      exact this

    rw [map_sum]
    have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
      rw [SchwartzMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]; rfl
    rw [hs]
    apply mul_right_cancel₀ hc0
    rw [hx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end GlobalTheory.ArchBij
end
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
namespace GlobalTheory.EvKer

theorem ker_trivial : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  intro F _ _ κ _ e ei ev hSB hstd hpure hinj v ψ hψ hev
  classical
  by_contra hne
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  set φ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ := Function.update (fun w => stdInd F κ w) v ψ with hφdef
  have hφSB : ∀ w, φ w ∈ SB (κ → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hψ
    · simpa [φ, Function.update_of_ne h, stdInd] using GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) w
  have hφev : ∀ᶠ w in cofinite, φ w = stdInd F κ w := by
    exact (Filter.eventually_cofinite_ne v).mono fun w h => by simp [φ, Function.update_of_ne h]
  have hmem : pure f₀ φ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hφSB (by simpa [stdInd] using hφev)
  have hcomp : (fun w => ev w (φ w)) = Function.update (fun w => ev w (stdInd F κ w)) v 0 := by
    funext w
    by_cases h : w = v
    · subst h; simp [φ, hev]
    · simp [φ, Function.update_of_ne h]
  have hevstd : ∀ᶠ w in cofinite, (fun w => ev w (stdInd F κ w)) w =
      {x : κ → Fv F w | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F w}.indicator 1 := by
    simpa [stdInd] using hstd
  obtain ⟨r, -, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f₀) _ hevstd
  have hzero : e (pure f₀ φ) = 0 := by
    rw [hpure f₀ φ hφSB hφev, hcomp, ← hr 0]
    funext x
    simp [tens]
  have h0 : pure f₀ φ = 0 := hinj hmem (Submodule.zero_mem _) (by rw [hzero, map_zero])
  have hall : ∀ w, φ w ≠ 0 := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hne
    · simp only [φ, Function.update_of_ne h]
      intro h1
      have := congrFun h1 0
      simp [stdInd, Set.indicator, zero_mem] at this
  have := GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ φ hall (by simpa [stdInd] using hφev) h0
  exact hf₀ (by rw [this]; rfl)

end GlobalTheory.EvKer
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridgeVac

theorem acts_eq {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => by
    simpa only [hz, Pi.smul_apply, Pi.zero_apply] using
      GlobalTheory.LatVac.at_liftV v (y i - evFin F v (x₀ i)) u hu
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem evFin_half_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) (2 : F)⁻¹ := by
    have h1 : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
      have := congrArg (evFin F v) (invOf_mul_self (2 : AF F))
      rwa [map_mul, map_ofNat, map_one] at this
    have h2 : algebraMap F (Fv F v) (2 : F)⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
    have h20 : (2 : Fv F v) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
    exact mul_right_cancel₀ h20 (h1.trans h2.symm)
  rw [e]
  exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers F v h

theorem vac_locVac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∃ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v ∧ s ≠ 0 ∧
      GlobalTheory.Hk3.LocVac ρ s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hLat, _⟩ := hC
  obtain ⟨hSB, hne, θ, _, hfix⟩ := hTr.geo.hM'.vac v
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hTr.base.inert v w hin).1
  have hb := evFin_half_mem v h2
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v (G.M'.vac v) hSB
  refine ⟨⟨G.M'.vac v, hSB⟩, rfl, fun h => hne (congrArg Subtype.val h), fun u hu => ?_⟩
  have hγ : κ u ∈ latAtV G.V' G.W v := (hLat u).1 hu
  have hone := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v θ
    (⅟(2 : AF F)) hb (κ u) hγ (κ u) hγ
  have h1 := hfix (κ u) hγ
  rw [hone, one_smul] at h1
  apply Subtype.ext
  exact acts_eq v hr hx₀ _ _ _ (hρ u ⟨G.M'.vac v, hSB⟩) h1

end GlobalTheory.InertBridgeVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairF

theorem brPairF_map_descent : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1)
    (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) =
      GlobalTheory.BrPairF.brPairF σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ _ v) := by
  intro K ι _ _ _ φ n N hN Λ σ u v
  rw [← brPair_mapVV φ σ hN Λ u v, brPair, LinearMap.compl₁₂_apply, brPairF_apply, GlobalTheory.BrRat.covOf_eq]

end GlobalTheory.BrPairF

end
end
