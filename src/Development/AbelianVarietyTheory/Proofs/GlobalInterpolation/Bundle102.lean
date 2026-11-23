module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle089
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle090
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle076
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle093
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle094
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle091
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC.TameGen

theorem part_pow {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  apply GlobalTheory.ParamLabel.Congr.part_pow <;> assumption

theorem pow_eq_of_part_eq {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x y : G} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y) :
    ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) := by
  obtain ⟨a, ha⟩ := part_pow hl hx
  obtain ⟨b, hb⟩ := part_pow hl hy
  refine ⟨a + b, ?_⟩
  have h1 : x ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ (a + b)) := by
    rw [pow_add, pow_mul, pow_mul, ha]
  have h2 : y ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l y ^ (l ^ (a + b)) := by
    rw [add_comm, pow_add, pow_mul, pow_mul, hb]
  rw [h1, h2, h]

def expo {m : ℕ} : Option (Fin m × Bool) → ℤ
  | none => 0
  | some (j, true) => (j.1 : ℤ) + 1
  | some (j, false) => -((j.1 : ℤ) + 1)

theorem expo_inj {m : ℕ} : Function.Injective (expo (m := m)) := by
  rintro (_ | ⟨i, _ | _⟩) (_ | ⟨j, _ | _⟩) h <;> simp only [expo] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (have : i = j := Fin.ext (by omega); rw [this])

theorem expo_bound {m : ℕ} (o : Option (Fin m × Bool)) : -(m : ℤ) ≤ expo o ∧ expo o ≤ m := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo]
  · omega
  · have := i.2; omega
  · have := i.2; omega

theorem tameList_eq {g m : ℕ} (w : (ZMod g)ˣ) (o : Option (Fin m × Bool)) :
    DC.tameList (fun j : Fin m => w ^ (2 * (j.1 + 1))) o = w ^ (2 * expo o) := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo, DC.tameList]
  · simp
  · rw [mul_neg, zpow_neg, ← zpow_natCast]; push_cast; rfl
  · rw [← zpow_natCast]; push_cast; rfl

theorem dvd_of_pow_eq {g m : ℕ} (w : (ZMod g)ˣ) {o o' : Option (Fin m × Bool)} (hne : o ≠ o') (k : ℕ)
    (h : (w ^ (2 * expo o)) ^ k = (w ^ (2 * expo o')) ^ k) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 4 * m ∧ orderOf w ∣ D * k := by
  have h1 : expo o ≠ expo o' := fun e => hne (expo_inj e)
  have b1 := expo_bound o
  have b2 := expo_bound o'
  refine ⟨(2 * expo o' - 2 * expo o).natAbs, by omega, by omega, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_eq_zpow_iff_modEq] at h
  have h2 := h.dvd
  rw [← sub_mul, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] at h2
  exact h2

theorem tameDistinct_gen : ∀ (r g m : ℕ) [Fact g.Prime] (w : (ZMod g)ˣ), orderOf w = g - 1 → 4 * (m : ℝ) * (g : ℝ) ^ ((1 : ℝ) / 4) < (g : ℝ) - 1 → 1 ≤ r → DC.TameDistinct r g (fun j : Fin m => w ^ (2 * (j.1 + 1))) := by
  intro r g m hg w hw hlt hr
  have hg2 : 2 ≤ g := hg.out.two_le
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hcast : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hq : (1 : ℝ) ≤ (g : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hgR (by norm_num)
  have hm0 : (0 : ℝ) ≤ 4 * (m : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro o o' h
    by_contra hne
    rw [tameList_eq, tameList_eq] at h
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne 1 (by rw [h])
    rw [mul_one, hw] at hdvd
    have h1 : g - 1 ≤ 4 * m := (Nat.le_of_dvd hD0 hdvd).trans hD
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    nlinarith
  · intro l hl hB o o' h
    by_contra hne
    apply hB
    simp only [tameList_eq] at h
    have hfin : ∀ u : (ZMod g)ˣ, IsOfFinOrder (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g)) := by
      intro u
      exact (((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom (ZMod g))).isOfFinOrder
        (isOfFinOrder_of_finite u))
    obtain ⟨a, ha⟩ := pow_eq_of_part_eq hl (hfin _) (hfin _) h
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at ha
    have ha' := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective ha)
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne _ ha'
    rw [hw] at hdvd
    have hn : g - 1 ≠ 0 := by omega
    set v := (g - 1).factorization l with hv
    set M := (g - 1) / l ^ v with hM
    have hmul : l ^ v * M = g - 1 := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
    have hMD : M ∣ D := (Nat.Coprime.pow_right a hcop).dvd_of_dvd_mul_right
      ((Dvd.intro_left _ hmul).trans hdvd)
    have hMle : M ≤ 4 * m := (Nat.le_of_dvd hD0 hMD).trans hD
    have h1 : g - 1 ≤ 4 * m * l ^ v := by
      rw [← hmul, mul_comm]; exact Nat.mul_le_mul_right _ hMle
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m * l ^ v : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    have h3 : (g : ℝ) ^ ((1 : ℝ) / 4) < (l : ℝ) ^ v := lt_of_mul_lt_mul_left (hlt.trans_le h2) hm0
    have h4 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 < ((l : ℝ) ^ v) ^ 4 :=
      pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
    have h5 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = g := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [h5, ← pow_mul, mul_comm] at h4
    refine Or.inr ⟨1, le_rfl, hr, hl, ?_⟩
    rw [pow_one, Nat.padicValNat_def, ← Nat.factorization_def _ hl, ← hv]
    exact_mod_cast h4
  · intro j
    exact ⟨w ^ (j.1 + 1), by rw [← pow_add, ← two_mul]⟩

end GlobalTheory.EX.DC.TameGen
end

section

namespace GlobalTheory.OverObj

theorem selfDualOverBase : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase :=
  GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice

end GlobalTheory.OverObj
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.exists_localBasis_snoc_of_localBasis : ∀ {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : N = n + 1) (t : E), t ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) → ∀ (p : ℕ) (B' : GL (Fin n) E), p.Prime → IsLocBasis p (L' : Set (Fin n → E)) B' → ∃ B : GL (Fin N) E, (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) ∧ (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) ∧ IsLocBasis p (L : Set (Fin N → E)) B := by
  first | exact @GlobalTheory.isLocBasis_snoc | exact GlobalTheory.isLocBasis_snoc | (intros; apply GlobalTheory.isLocBasis_snoc <;> assumption)
end

section

namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem fix_and_win_of_numAt (eps : ℝ) (C : FC) (Fm : FamP eps) (hS : Std C) (hO : Fm.cOut = C.cOut)
    (hN : ∀ x (i : Fm.Ix x), Nonempty (NumAt C (Fm.L x i))) : DC.PageFix Fm ∧ DC.PageWin Fm := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, sCt⟩, sCc, -, -, scw, sCYL, -, sCp, seP, scTO, -, sCe, -⟩ := hS
  simp only [FamP.cOut, FC.cOut, List.cons.injEq] at hO
  obtain ⟨oCt, oCc, -, -, -, ocw, oCYL, -, -, -, oCp, oeP, ocTO, -, oCe, -⟩ := hO
  refine ⟨⟨oCp.trans sCp, oeP.trans seP, ?_, ?_, oCe.trans sCe, oCc.trans sCc, ocw.trans scw, oCYL.trans sCYL,
    fun x hx i => ?_⟩, fun x hx i => ?_⟩
  · rw [ocTO, oeP, scTO, seP]; norm_num
  · rw [ocTO, oCt, scTO, sCt]; norm_num
  · obtain ⟨N⟩ := hN x i
    refine ⟨N.ccK_top, N.cloud1, N.g_le, N.pde_lt.1, N.pde_lt.2, N.logFiveDepth_eq, ?_, ?_⟩
    · have h := N.Lw_eq
      rw [Fm.L_x x i hx, Fm.L_eps x i, ← oCt] at h
      exact h
    · have h := (Fm.parT x hx i).TO_eq
      rw [Fm.parT_cTO, Fm.L_x x i hx] at h
      exact h
  · obtain ⟨N⟩ := hN x i
    have h := N.win
    rw [Fm.L_x x i hx, Fm.L_eps x i] at h
    exact h

end GlobalTheory.EX.DC
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem has_withDuty_wall_and_choices {Q : PtProp} {C : FC} {cD ch C8 C5 c6 Cb : ℝ} (p : Pt C) {R : Ranks} {H : Host R} {q0 : ℕ}
    {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (hC : Std C) (hT : H.CT2 = C.CT2)
    (hH : HostGood p.L.sc C8 C5 c6 Cb H q0) (hq : (q0 : ℝ) < p.L.sc.X')
    (h0 : ∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) (hW : WOK p.L.sc cD ch C.GK H a b)
    (hV : Val C cD ch p.L) (hF : p.From H a b c u0) (hI : CanonInst p.ta.Gx) (hQ : p.Has Q) :
    p.Has ((withDuty Q).and WallPt) ∧ ThickSetLowerBound p.L ∧ ChBad_at p.ta.Gx Cb ∧ ChQD_at p.D p.L.sc.x p.L.sc.eps C5 := by
  have hw := GlobalTheory.EX.wreq_of_wok C cD ch p R H a b M c u0 hC hV hF hI h0 hW
  obtain ⟨hv, -, hT2, -, hQD, hBox, -, -, hBad, -, -, -, ⟨hp, hmod, -, hne, hne'⟩, hlev⟩ := hH
  have hb := GlobalTheory.EX.chBad_of_from C p R H a b M c u0 Cb hF hI hBad
  have eS := hF.QS_eq
  have hBW := hF.boxesW hBox
  have hQW := hF.qdRowsW hBox
  obtain ⟨eR, -, eT2, eq, ed, eg, ep, ep', hsub, -⟩ := hF
  subst eR
  have hq0 : (0 : ℝ) < q0 := by exact_mod_cast hp.pos
  have hXb := X'_le_b p.L.sc
  refine ⟨⟨⟨hQ, hw, ?_, ?_, q0, hsub (by rw [hlev]; simp), hp, ?_, ?_, hq, ?_, ?_, ?_⟩,
    ⟨hV.mem_box.1, hV.mem_box.2, hw⟩⟩, ?_, hb, ?_⟩
  · exact hBW
  · exact hQW
  · rw [eS, eq, ed]; exact hmod
  · rw [Real.log_le_iff_le_exp hq0]
    exact hq.le.trans hXb
  · rw [ep]; exact hne
  · rw [ep']; exact hne'
  · intro i hi
    have hg := (hv.2.2.2.2.1 i).1
    rw [← eg, ← hi] at hg
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  · unfold ThickSetLowerBound Host.secondSet_card_lower_bound
    rw [eT2, hV.secondConstant_eq, hV.host.2.2.2.2.2.1, ← hT, ← hv.2.2.2.2.2.1]
    exact hT2
  · unfold ChQD_at
    rw [eq, ed]
    exact hQD

end GlobalTheory.EX.DC
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), Differentiable ℂ G → Bd 1 (hat ι (C ω * logS) G) → MomInt ι (fun _ : Unit => ι.symm ω) G := by
  first | exact @GlobalTheory.MomOneAmice.momInt_of_bd_hat | exact GlobalTheory.MomOneAmice.momInt_of_bd_hat | (intros; apply GlobalTheory.MomOneAmice.momInt_of_bd_hat <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ a b : Fin N, a ≠ b → ∀ f ∈ M, rowE k N N a b f ∈ M := by
  first | exact @GlobalTheory.Alc.rowE_mem_of_isGLSubmodule | exact GlobalTheory.Alc.rowE_mem_of_isGLSubmodule | (intros; apply GlobalTheory.Alc.rowE_mem_of_isGLSubmodule <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  refine SzRow.imp (SzRow.and szRow_eta_bounds (SzRow.and szRow_eta_le_w szRow_rbS)) ?_
  rintro C cD ch D L - - ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
  exact ⟨h3, h1, h2, h4, h5, h6, h7, h8, h10⟩

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD hcD => ⟨1300 + cD, fun ch hch => ⟨max x1 200, fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (D.R.r : ℝ) + D.R.m * D.R.t ≤ D.R.N D.R.m := by
    have : D.R.r + D.R.m * D.R.t ≤ D.R.N D.R.m := by
      unfold Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ L.etaSz / D.R.m := by
    have e : L.etaSz / D.R.m = (h0v L.sc ch : ℝ) := by
      rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ L.etaSz / D.R.m := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch)
  have hth : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : szTh L ≤ 1 := by unfold szTh; rw [hε]; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hxone this
  obtain ⟨a1, a2, a3, a5, a6, a7, -, a9, -⟩ := nodeGap_poly hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m))
    (by positivity : (0 : ℝ) ≤ (D.R.r : ℝ) + D.R.m * D.R.t) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hth hth hH
  refine ⟨?_, a2, a3, a5, a6, a7, a9⟩
  have hb : 0 < L.sc.b := by unfold Scale.b; positivity
  refine le_trans (le_of_eq ?_) a1
  unfold szlStar
  rw [div_div_eq_mul_div]
  field_simp

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_sizeCond_sizeQD_sizePde : SzRow (fun _ _ L => SizeCond L ∧ SizeQD L ∧ SizePde L) := by
  first | exact @GlobalTheory.EX.szRow_cond_qd_pde | exact GlobalTheory.EX.szRow_cond_qd_pde | (intros; apply GlobalTheory.EX.szRow_cond_qd_pde <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_exists_Y_bounds_host_g_mem_Icc_Y_two_mul_Y : SzRow (fun C D L => (∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ Y ^ ((1 : ℝ) / 4) ∧ Real.log Y ≤ C.P.CYL * L.sc.L ∧ ∀ i, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y)) := by
  first | exact @GlobalTheory.EX.szRow_typePrimes | exact GlobalTheory.EX.szRow_typePrimes | (intros; apply GlobalTheory.EX.szRow_typePrimes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_TOv_sq_le_del_and_gap_mul_le_del : SzRow (fun C D L => ((((TOv L.sc : ℕ) : ℝ)) ^ 2 ≤ ((D.s.Del : ℚ) : ℝ)) ∧ ((((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2) * (((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2 + 2 * (D.R.N D.R.m : ℝ)) ≤ ((D.s.Del : ℚ) : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_Del_TO_gap | exact GlobalTheory.EX.szRow_Del_TO_gap | (intros; apply GlobalTheory.EX.szRow_Del_TO_gap <;> assumption)
end
