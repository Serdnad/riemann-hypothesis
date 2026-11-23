module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylConjugateOfUnitarySatakeDiagDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle165
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle167
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc.Unif

theorem exists_h90_eq_oneOff_of_normOne_at_split_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F), (∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x)) → ∀ (π : (AfE F E)ˣ), π ∈ U1 σ → OneOff w π → ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x := by
  intro F E _ _ _ _ _ σ w spl hsig π hπ hoff
  set p : E ⊗[F] w.adicCompletion F := prV (E := E) w (π : AfE F E) with hp
  have hπe : (π : AfE F E) = oneAt w p := ext_prV fun w' => by
    by_cases h : w' = w
    · subst h; rw [prV_oneAt_self]
    · rw [prV_oneAt_ne w w' h]; exact hoff w' h
  have hU : (π : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (π : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) ((MonoidHom.mem_ker).1 hπ)
    simpa [conjId] using this
  have hp1 : p * sigR σ (w.adicCompletion F) p = 1 := by
    have h2 := congrArg (prV (E := E) w) hU
    rw [hπe, sigR_oneAt, oneAt_mul, prV_oneAt_self, map_one] at h2
    exact h2
  have hab : (spl p).1 * (spl p).2 = 1 ∧ (spl p).2 * (spl p).1 = 1 := by
    have h3 := congrArg spl hp1
    rw [map_mul, hsig, map_one] at h3
    exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
  let c : (E ⊗[F] w.adicCompletion F)ˣ :=
    ⟨spl.symm ((spl p).1, 1), spl.symm ((spl p).2, 1),
      by rw [← map_mul]; apply spl.injective; rw [RingEquiv.apply_symm_apply, map_one]; exact Prod.ext hab.1 (mul_one _),
      by rw [← map_mul]; apply spl.injective; rw [RingEquiv.apply_symm_apply, map_one]; exact Prod.ext hab.2 (mul_one _)⟩
  refine ⟨oneAtU w c, ?_, fun w' hw' => prV_oneAt_ne w w' hw' _⟩
  apply Units.ext
  have hval : ((h90 σ (oneAtU w c) : (AfE F E)ˣ) : AfE F E) =
      oneAt w (c : E ⊗[F] w.adicCompletion F) *
        sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt w ((c⁻¹ : (E ⊗[F] w.adicCompletion F)ˣ) : E ⊗[F] w.adicCompletion F)) := by
    simp only [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, conjId, map_inv]
    rfl
  rw [hval, sigR_oneAt, oneAt_mul, hπe]
  congr 1
  apply spl.injective
  rw [map_mul, hsig]
  show spl (spl.symm ((spl p).1, 1)) * swapR (w.adicCompletion F) (spl (spl.symm ((spl p).2, 1))) = spl p
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  show ((spl p).1 * 1, 1 * (spl p).2) = spl p
  rw [mul_one, one_mul]

end GlobalTheory.TwV.Xc.Unif
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.exists_normOne_idele_order_one_trivial_elsewhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  first | exact @GlobalTheory.TwV.Xc.Unif.exists_unif | exact GlobalTheory.TwV.Xc.Unif.exists_unif | (intros; apply GlobalTheory.TwV.Xc.Unif.exists_unif <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_qbar {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (q : TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (algebraMap TaylorLogMetric.Qbar ℂ q) = lam q := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left (show algebraMap TaylorLogMetric.Qbar ℂ q ∈ TaylorLogMetric.Qbar from q.2)]
  rfl

theorem kapG_eq_char_inf : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (a : D.host.E), a * D.host.conj a = 1 → (∀ v, (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det = ρ v a) → letI := wittFractionAlgebraCp p; letI := algKfC E; kapG X ℂ_[p] j c γ = E.iK (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) * TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) * (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
  intro D p _ X E pos lam ρ hLP j c γ a ha hdet
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact zero_ne_one ha
  have hconj : D.host.conj a = a⁻¹ := eq_inv_of_mul_eq_one_right ha

  have hcA : cA X ℂ_[p] j (gamAt X j c γ) =
      TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) := by
    let q : ∀ v : X.Pl, Fin (X.G.P.n' v) → TaylorLogMetric.Qbar := fun v s => ⟨TaylorLogMetric.embT D (pos ⟨v, s⟩) a, embT_mem_qbar D _ a⟩
    have h1 : (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) =
        algebraMap TaylorLogMetric.Qbar ℂ (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), q v s ^ X.w v (j + 1) s) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_zpow₀]
      rfl
    rw [h1, lamC_qbar, map_prod]
    unfold cA
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_zpow₀, hdet v]
    have h2 : lam (q v s) = twG X E v s (ρ v (if IsOddPos s then D.host.conj a else a)) := by
      rw [← hLP v s a, ← lamC_qbar lam (q v s)]
      rfl
    rw [h2, twG_eq_tw]
    by_cases hs : IsOddPos s
    · rw [if_pos hs, if_pos hs, hconj, map_inv₀, map_inv₀, inv_zpow', neg_one_mul]
    · rw [if_neg hs, if_neg hs, one_mul]
  have hP : (∏ v : X.Pl, (p : ℂ_[p]) ^ (-(X.vm v (j + 1) * ordP (X.G.P.W v) p
      (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))) =
      (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
    simp_rw [hdet]
    rw [← Finset.sum_neg_distrib]
    induction (Finset.univ : Finset X.Pl) using Finset.cons_induction with
    | empty => simp
    | cons b s hb ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hp, ih]
  unfold kapG
  rw [hcA, hP]
  rfl

end GlobalTheory.TwV.Xc

end
end

section

noncomputable section

namespace GlobalTheory.SatBcInj

open Formalism.UG GlobalTheory.InertThetaCompare GlobalTheory.LFun.Orbit Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting (labInd)
open GlobalTheory.LGrp (WeylConjU bcParam bcParam_of_weylConj)

variable {m : ℕ}

def monoJ (a : Fin m → ℤ) (γ : Fin m → ℂ) : ℂ := ∏ i, γ i ^ a i

def actJ (w : Sgn m) (γ : Fin m → ℂ) : Fin m → ℂ := fun i => γ (w.1 i) ^ (w.2 i : ℤ)

def evJ (c : (Fin m → ℤ) →₀ ℂ) (γ : Fin m → ℂ) : ℂ := ∑ a ∈ c.support, c a * monoJ a γ

def symJ (a : Fin m → ℤ) (γ : Fin m → ℂ) : ℂ := ∑ w : Sgn m, monoJ a (actJ w γ)

theorem monoJ_act (w : Sgn m) (a : Fin m → ℤ) (γ : Fin m → ℂ) : monoJ a (actJ w γ) = monoJ (coact w a) γ := by
  unfold monoJ
  rw [← Equiv.prod_comp w.1 fun i => γ i ^ coact w a i]
  simp [actJ, coact, zpow_mul]

def coinv (w : Sgn m) (b : Fin m → ℤ) : Fin m → ℤ := fun i => w.2 i * b (w.1 i)

theorem coact_coinv (w : Sgn m) (b : Fin m → ℤ) : coact w (coinv w b) = b := funext fun j => by
  simp only [coact, coinv, Equiv.apply_symm_apply, ← mul_assoc]
  rcases Int.units_eq_one_or (w.2 (w.1.symm j)) with h | h <;> simp [h]

theorem coinv_coact (w : Sgn m) (a : Fin m → ℤ) : coinv w (coact w a) = a := funext fun j => by
  simp only [coact, coinv, Equiv.symm_apply_apply, ← mul_assoc]
  rcases Int.units_eq_one_or (w.2 j) with h | h <;> simp [h]

theorem evJ_act {c : (Fin m → ℤ) →₀ ℂ} (hc : ∀ w a, c (coact w a) = c a) (w : Sgn m) (γ : Fin m → ℂ) :
    evJ c (actJ w γ) = evJ c γ := by
  unfold evJ
  simp only [monoJ_act]
  refine Finset.sum_nbij' (coact w) (coinv w) (fun a ha => ?_) (fun b hb => ?_) (fun a _ => coinv_coact w a)
    (fun b _ => coact_coinv w b) (fun a _ => by rw [hc])
  · rw [Finsupp.mem_support_iff, hc]; exact Finsupp.mem_support_iff.1 ha
  · rw [Finsupp.mem_support_iff, ← hc w, coact_coinv]; exact Finsupp.mem_support_iff.1 hb

theorem sum_symJ {c : (Fin m → ℤ) →₀ ℂ} (hc : ∀ w a, c (coact w a) = c a) (γ : Fin m → ℂ) :
    ∑ a ∈ c.support, c a * symJ a γ = Fintype.card (Sgn m) * evJ c γ := by
  simp only [symJ, Finset.mul_sum]
  have e : ∀ w : Sgn m, ∑ a ∈ c.support, c a * monoJ a (actJ w γ) = evJ c γ := fun w => evJ_act hc w γ
  rw [Finset.sum_comm, Finset.sum_congr rfl fun w _ => e w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem symJ_coact (w : Sgn m) (a : Fin m → ℤ) (γ : Fin m → ℂ) : symJ (coact w a) γ = symJ a γ := by
  let φ : Sgn m → Sgn m := fun u => (u.1 * w.1, fun i => u.2 (w.1 i) * w.2 i)
  have hφ : Function.Injective φ := fun u u' h => Prod.ext (mul_right_cancel (congrArg Prod.fst h))
    (funext fun i => by simpa [φ] using congrFun (congrArg Prod.snd h) (w.1.symm i))
  refine Fintype.sum_bijective φ (Finite.injective_iff_bijective.1 hφ) _ _ fun u => ?_
  rw [← monoJ_act]
  congr 1
  funext i
  simp [actJ, φ, zpow_mul]

theorem eq_zero_of_triangular (H : (Fin m → ℤ) → ℕ) (c : (Fin m → ℤ) → (Fin m → ℤ) →₀ ℂ)
    (hcoef : ∀ d, Dom d → ∀ w a, c d (coact w a) = c d a) (hself : ∀ d, Dom d → c d d ≠ 0)
    (htri : ∀ d a, Dom d → Dom a → c d a ≠ 0 → a = d ∨ H a < H d) (S : (Fin m → ℤ) → ℂ)
    (hS : ∀ w a, S (coact w a) = S a) (h : ∀ d, Dom d → ∑ a ∈ (c d).support, c d a * S a = 0) :
    ∀ d, Dom d → S d = 0 := fun d => by
  classical
  induction hk : H d using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    intro hd
    have h3 := h d hd
    rw [← Finset.sum_filter_ne_zero, Finset.sum_congr rfl (g := fun _ => c d d * S d),
      Finset.sum_const, smul_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h3
    · refine (mul_eq_zero.1 (h3.elim (fun h4 => ?_) id)).resolve_left (hself d hd)
      exact not_not.1 (h4 (Finsupp.mem_support_iff.2 (hself d hd)))
    · intro a ha
      obtain ⟨w, hw⟩ := exists_dom a
      have h5 := (Finset.mem_filter.1 ha).2
      rw [← hcoef d hd w a, ← hS w a] at h5 ⊢
      rcases htri d _ hd hw (left_ne_zero_of_mul h5) with e | e
      · rw [e]
      · exact absurd (ih _ (hk ▸ e) _ rfl hw) (right_ne_zero_of_mul h5)

theorem monoJ_single (i₀ : Fin m) (k : ℕ) (δ : Fin m → ℂ) : monoJ (Pi.single i₀ (k : ℤ)) δ = δ i₀ ^ k := by
  unfold monoJ
  rw [Finset.prod_eq_single i₀ (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

theorem dom_single (i₀ : Fin m) (h0 : (i₀ : ℕ) = 0) (k : ℕ) : Dom (Pi.single i₀ (k : ℤ)) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp only [Pi.single_apply]
    have : a ≤ b := hab
    rw [Fin.le_def] at this
    split_ifs with h1 h2 h2 <;> first | rfl | omega | (subst h2; exfalso; exact h1 (Fin.ext (by omega)))
  · simp only [Pi.single_apply]; split_ifs <;> omega

theorem ne_zero_of_symJ (α : Fin m → ℂˣ) (α₀ : Fin m → ℂ) (i₀ : Fin m)
    (h : ∀ k : ℕ, symJ (Pi.single i₀ (k : ℤ)) α₀ = symJ (Pi.single i₀ (k : ℤ)) fun j => (α j : ℂ)) (i : Fin m) :
    α₀ i ≠ 0 := by
  classical
  intro hi
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp _ (powersHom ℂ).injective
  have e : ∑ w : Sgn m, Finsupp.single (actJ w α₀ i₀) (1 : ℂ) =
      ∑ w : Sgn m, Finsupp.single (actJ w (fun j => (α j : ℂ)) i₀) (1 : ℂ) := by
    refine hli (funext fun k => ?_)
    have := h k.toAdd
    simp only [symJ, monoJ_single] at this

    simpa [map_sum, powersHom_apply] using this
  have h1 := DFunLike.congr_fun e 0
  rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply, Finset.sum_eq_zero (s := Finset.univ)
    (f := fun w : Sgn m => (Finsupp.single (actJ w (fun j => (α j : ℂ)) i₀) (1 : ℂ)) 0) fun w _ =>
      Finsupp.single_eq_of_ne (zpow_ne_zero _ (Units.ne_zero _)).symm] at h1
  simp only [Finsupp.single_apply, Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ (Equiv.swap i₀ i, 1)) (by simp [actJ, hi])

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}
  [CompleteSpace L]

theorem ne_zero_of_dosetInd (hU : IsUnramInv ϖ σ q) (α : Fin (n / 2) → ℂˣ) (α₀ : Fin (n / 2) → ℂ)
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) α₀)
    (i : Fin (n / 2)) : α₀ i ≠ 0 := by
  classical
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let x : (Fin (n / 2) → ℤ) → ℂ := fun a => ∏ i, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
  have hx : ∀ a, x a ≠ 0 := fun a => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq
  have hex : ∀ d : Fin (n / 2) → ℤ, ∃ c : (Fin (n / 2) → ℤ) →₀ ℂ, Dom d →
      ∀ a, c a = x a * cnt σ n ϖ (lab n d) a := fun d => by
    by_cases hd : Dom d
    · exact ⟨Finsupp.ofSupportFinite (fun a => x a * cnt σ n ϖ (lab n d) a)
        ((finite_cnt hU (good_lab hd)).subset fun a ha h0 => ha (by simp [h0])), fun _ _ => rfl⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using hex
  have hevJ : ∀ d, Dom d → ∀ γ : Fin (n / 2) → ℂ,
      evJ (c d) γ = SatU ϖ q (labInd σ n ϖ (lab n d)) γ := fun d hd γ => by
    rw [satU_labInd hU (good_lab hd), finsum_eq_sum_of_support_subset (s := (c d).support), evJ]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [hc d hd, Finset.prod_mul_distrib]
      simp only [monoJ, x]
      ring
    · intro a ha
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hc d hd]
      exact mul_ne_zero (hx a) (right_ne_zero_of_mul ha)
  have hcoef : ∀ d, Dom d → ∀ w a, c d (coact w a) = c d a := fun d hd w a => by
    refine coeff_coact (fun γ => ?_) a
    obtain ⟨t, ht⟩ := exists_diag hU (good_lab hd)
    change evJ (c d) (fun i => ((act w γ i : ℂˣ) : ℂ)) = evJ (c d) (fun i => (γ i : ℂ))
    rw [hevJ d hd, hevJ d hd, labInd_eq_dosetInd ht]
    exact (GlobalTheory.LFun.satU_of_weylConj hU (Final.DosetIndMem _ _ _ _) (weylConj_act w γ)).symm
  have hJ : ∀ d, Dom d → evJ (c d) α₀ = evJ (c d) (fun i => (α i : ℂ)) := fun d hd => by
    obtain ⟨t, ht⟩ := exists_diag hU (good_lab hd)
    rw [hevJ d hd, hevJ d hd, labInd_eq_dosetInd ht]
    exact (h _ t (anti_getD (good_lab hd).1 (good_lab hd).2.1) ht).symm
  let T : (Fin (n / 2) → ℤ) → Fin n → ℤ := fun d k => ∑ i ∈ Finset.Ici k, (lab n d).getD i.1 0
  have h2 := eq_zero_of_triangular (fun d => (-∑ k, T d k).toNat) c hcoef (fun d hd => ?_)
    (fun d a hd ha h0 => ?_) (fun a => symJ a α₀ - symJ a fun j => (α j : ℂ))
    (fun w a => by simp only [symJ_coact]) (fun d hd => ?_)
  · have hi0 : 0 < n / 2 := Nat.pos_of_ne_zero fun h0 => (h0 ▸ i).elim0
    refine ne_zero_of_symJ α α₀ ⟨0, hi0⟩ (fun k => sub_eq_zero.1 (h2 _ (dom_single _ rfl k))) i
  · have := cnt_self hU (good_lab hd)
    rw [getD_lab] at this
    rw [hc d hd]
    exact mul_ne_zero (hx d) (by exact_mod_cast this)
  · rw [hc d hd] at h0
    have h1 : ∀ k, T d k ≤ T a k := tail_of_cnt hU (good_lab ha) (good_lab hd) (by
      rw [getD_lab]; exact_mod_cast right_ne_zero_of_mul h0)
    have h2 : ∑ k, T a k ≤ 0 := Finset.sum_nonpos fun k _ => tail_nonpos (good_lab ha) k
    rcases (Finset.sum_le_sum (s := Finset.univ) fun k _ => h1 k).eq_or_lt with e | e
    · have h3 := eq_of_tails fun k => (Finset.sum_eq_sum_iff_of_le fun k _ => h1 k).1 e k (Finset.mem_univ k)
      rw [← getD_lab a, ← getD_lab d, eq_of_getD (good_lab hd).1 (good_lab ha).1 (congrFun h3)]
      exact Or.inl rfl
    · exact Or.inr (by omega)
  · simp only [mul_sub, Finset.sum_sub_distrib, sum_symJ (hcoef d hd), hJ d hd, sub_self]

theorem bcParam_eq_ubc_of_satU_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂˣ) (α₀ : Fin (n / 2) → ℂ),
    (∀ (d : Fin n → ℤ) (t : Formalism.UG.GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) (fun i => (α i : ℂ)) =
        Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) α₀) →
    (GlobalTheory.LGrp.bcParam n α).map (fun a : ℂˣ => (a : ℂ)) = ubc n (Finset.univ.val.map α₀) := by
  intro L _ _ _ ϖ σ q n hU α α₀ h
  let β : Fin (n / 2) → ℂˣ := fun i => Units.mk0 (α₀ i) (ne_zero_of_dosetInd hU α α₀ h i)
  have hβ : (fun i => ((β i : ℂˣ) : ℂ)) = α₀ := funext fun i => Units.val_mk0 _
  have e : bcParam n α = bcParam n β :=
    bcParam_of_weylConj (GlobalTheory.LFun.weylConj_of_dosetInd hU (by rw [hβ]; exact h))
  rw [e, bcParam, ubc]
  simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, Units.val_inv_eq_inv_val, Multiset.map_replicate,
    Units.val_one]
  rw [← hβ]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · rw [h2, if_neg (Nat.not_odd_iff.2 h2)]; rfl
  · rw [h2, if_pos (Nat.odd_iff.2 h2)]; rfl

end Local

end GlobalTheory.SatBcInj

end
end

section

open Matrix

theorem _root_.GlobalTheory.T.integral_gramCorrection_skewHermitian_maximal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n r : ℕ) (JS a : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  (∀ k, 1 ≤ e k) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) i j ∈ Formalism.UG.intL L) ∧ (∀ i j, ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    ∀ i j, Valued.v ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) i j) < 1 := by
  first | exact @GlobalTheory.Hk3.GramSep.eint | exact GlobalTheory.Hk3.GramSep.eint | (intros; apply GlobalTheory.Hk3.GramSep.eint <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitianDual_subset_of_integral_gram : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ v : Fin n → L,
      (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) u v ∈ Formalism.UG.intL L) →
      (∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w) v ∈ Formalism.UG.intL L) →
      ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w := by
  first | exact @GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int | exact GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int | (intros; apply GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitianForm_integral_preimage_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.GramA.hform_integral | exact GlobalTheory.Hk3.HoweG.GramA.hform_integral | (intros; apply GlobalTheory.Hk3.HoweG.GramA.hform_integral <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.selfDual_lattice_eq_unitary_mul_integralGL : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (JS : GL (Fin n) L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
      ∃ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), ∃ k : GL (Fin n) L, k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        a = (g : GL (Fin n) L) * k := by
  first | exact @GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int | exact GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int | (intros; apply GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.selfDual_one_add_skewHermitian_mul_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n : ℕ) (JS a k : GL (Fin n) L) (E : Matrix (Fin n) (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) → (∀ i j, E i j ∈ Formalism.UG.intL L) →
  (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (k : Matrix (Fin n) (Fin n) L) = 1 + E →
  (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.SelfDual σ JS (k * a) := by
  first | exact @GlobalTheory.SelfDualUnip.selfDual_mul_of_skew | exact GlobalTheory.SelfDualUnip.selfDual_mul_of_skew | (intros; apply GlobalTheory.SelfDualUnip.selfDual_mul_of_skew <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.cayley_transform_integral_unitary_congruent_one : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  first | exact @GlobalTheory.Hk3.CayleyCong.cayley_cong | exact GlobalTheory.Hk3.CayleyCong.cayley_cong | (intros; apply GlobalTheory.Hk3.CayleyCong.cayley_cong <;> assumption)
end
