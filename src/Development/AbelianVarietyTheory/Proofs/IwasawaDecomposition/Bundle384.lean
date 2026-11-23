module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTie

section

variable {L : Type} [Field L] [NumberField L]

def Good (F : Type) [Field F] [NumberField F] [Algebra F L] (χ : HChar L) : Prop :=
  (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) ∧ χ.TrivOn F ∧ ∀ v, χ.TameAt v

variable {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem resFin_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    (χ * χ').resFin v k = χ.resFin v k * χ'.resFin v k := by
  simp only [HChar.resFin, MonoidHom.finsetProd_apply, ← Finset.prod_mul_distrib]
  rfl

omit [NumberField F] in
theorem resInf_mul (χ χ' : HChar L) (v : InfinitePlace F) (k : Fˣ) :
    (χ * χ').resInf v k = χ.resInf v k * χ'.resInf v k := by
  simp only [HChar.resInf, MonoidHom.finsetProd_apply, ← Finset.prod_mul_distrib]
  rfl

theorem good_one : Good F (1 : HChar L) := by
  refine ⟨⟨1, one_pos, one_pow 1⟩, ⟨fun v k => ?_, fun v k => ?_⟩, fun _ _ _ _ => rfl⟩
  · simp only [HChar.resFin, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun _ _ => rfl
  · simp only [HChar.resInf, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem Good.mul {χ χ' : HChar L} (h : Good F χ) (h' : Good F χ') : Good F (χ * χ') := by
  obtain ⟨⟨n, hn, h1⟩, h2, h3⟩ := h
  obtain ⟨⟨n', hn', h1'⟩, h2', h3'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ⟨fun v k => ?_, fun v k => ?_⟩, fun v x hx hx' => ?_⟩
  · unfold HChar.OrderDvd at *
    rw [mul_pow, pow_mul, h1, one_pow, pow_mul', h1', one_pow, one_mul]
  · rw [resFin_mul, h2.1, h2'.1, one_mul]
  · rw [resInf_mul, h2.2, h2'.2, one_mul]
  · change χ.loc v x * χ'.loc v x = 1
    rw [h3 v x hx hx', h3' v x hx hx', one_mul]

end

theorem good_set {B : Base} (f : Fr B.toPre) (T : TwDat B) {χ : HChar B.host.E} (h : χ ∈ T.set f) : Good B.host.F χ := by
  have hd : Good B.host.F f.del := ⟨f.isDel.fin, f.isDel.triv, f.isDel.tame⟩
  have hd' : Good B.host.F f.del' := ⟨f.isDel'.fin, f.isDel'.triv, f.isDel'.tame⟩
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact good_one
  · exact hd
  · exact hd'
  · have hp : Good B.host.F (T.psi w) := ⟨(T.psi_tw w).1, (T.psi_tw w).2.1, (T.psi_tw w).2.2.1⟩
    unfold TwDat.xiTw
    split_ifs
    · exact hd'.mul hp
    · exact hd.mul hp

end GlobalTheory.Mem.Top.TupTie
end

section

noncomputable section

namespace GlobalTheory.Mem.SProv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem delv_pos (s : Scale) (cD : ℝ) : (0 : ℚ) < (Delv s cD : ℚ) := by
  have h : 0 < s.x ^ cD := Real.rpow_pos_of_pos (lt_trans one_pos s.one_lt_alt) _
  exact_mod_cast Nat.ceil_pos.2 h

theorem code_of_over (K : Ctx) (B : Pre) (h : K.Over B) :
    ∃ letter : B.Word → Fin (B.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l + 1 < B.R.k - 1),
        (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv K.s K.cD : ℚ)) ∧
      ∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l < B.R.k - 2),
        (B.hcW w τ).u ⟨l + 1, by omega⟩ =
          (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv K.s K.cD : ℚ) else 0) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨K.c, K.ok.inj, fun w τ l h => ?_, K.ok.code⟩
  have h' : l + 1 < K.P.R.k - 1 := h
  have a := (K.ok.hc w).1 τ ⟨l, by omega⟩
  have b := (K.ok.hc w).1 τ ⟨l + 1, h'⟩
  have e : K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 := by omega
  show (K.P.hcW w τ).v ⟨l, _⟩ - (K.P.hcW w τ).v ⟨l + 1, h'⟩ = _
  rw [a, b]
  simp only [e]
  push_cast
  ring

theorem exists_split (B : Pre) (p : HeightOneSpectrum (𝓞 B.host.F)) (L : LocAt B.host.F B.host.E B.conjF p) :
    ∃ s : Option (SplitAt L.Fp L.Ep L.cj (resChar p)),
      (s.isSome ↔ resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  letI := B.host.cmStar
  by_cases h : resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · have hk : ∃ k, resChar p = B.host.g k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact ⟨_, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt B.host.F B.host.E B.conjF B.sp.cm.deg2 (SpectralModel.conjF_ne B) p L
      (by rw [hk, SpectralModel.ncard_primesOver _ _ (B.host.g_prime k), B.g_split])
    exact ⟨some S, by simpa using h⟩
  · exact ⟨none, by simp [h]⟩

theorem exists_sStage_loc (K : Ctx) (B : Base) (C : Cols B) (W : RowsRest B C) (cd : CDHaar) (h : K.Over B.toPre)
    (h2 : SpectralModel.ColsPos C) (h3 : W.Drows ≤ W.Dall)
    (L : ∀ p : HeightOneSpectrum (𝓞 B.host.F), LocAt B.host.F B.host.E B.toPre.conjF p) :
    ∃ S : SStage B C W, S.s.Del = (Delv K.s K.cD : ℚ) ∧ S.s.cdScale = Vol.trueScale cd ∧
      (∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)) ∧
      ∀ p, ∃ s, S.s.atP p = { L p with split := s } := by
  obtain ⟨letter, hl, hg, hu⟩ := code_of_over K B.toPre h
  obtain ⟨S, hd, -⟩ := SpectralModel.exists_sStage W ⟨_, letter, delv_pos K.s K.cD, hl, hg, hu⟩ h2 h3
    (fun τ => Vol.trueDsig B.R (B.hc τ)) (fun τ => (Vol.lamSH_isHCParam_and_trueDsig_pos B.R (B.hc τ)).2) (fun _ => 0)
  choose sp hsp using fun p => exists_split B.toPre p (L p)
  exact ⟨{ S with
      s := { S.s with
        cdScale := Vol.trueScale cd
        cdScale_pos := Vol.trueScale_pos cd
        Del := (Delv K.s K.cD : ℚ)
        Del_pos := delv_pos K.s K.cD
        cloud_gap := hg
        letter := letter
        letter_inj := hl
        u_letter := hu
        atP := fun p => { L p with split := sp p } }
      s_split := hsp
      s_HH := S.s_HH
      s_Cu := S.s_Cu
      s_PlF := S.s_PlF
      s_Cu_isom := S.s_Cu_isom
      sEE := S.sEE },
    rfl, rfl, fun τ => congrFun hd τ, fun p => ⟨sp p, rfl⟩⟩

end GlobalTheory.Mem.SProv

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TamePow

theorem four_mul_root_lt {m k g : ℝ} (hm : 2 ≤ m) (hk : m + 3 ≤ k) (hg : k ^ 8 ≤ g) :
    4 * m * g ^ ((1 : ℝ) / 4) < g - 1 := by
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  set t := g ^ ((1 : ℝ) / 4) with ht
  have ht4 : t ^ 4 = g := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hg0]
    norm_num
  have hkt : k ^ 2 ≤ t := by
    have h8 : (k ^ 8) ^ ((1 : ℝ) / 4) ≤ t := Real.rpow_le_rpow (by positivity) hg (by norm_num)
    have e : (k ^ 8) ^ ((1 : ℝ) / 4) = k ^ 2 := by
      rw [show (k ^ 8 : ℝ) = (k ^ 2) ^ (4 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have ht25 : 25 ≤ t := by nlinarith
  have h1 : 4 * m * t < k ^ 2 * t := by
    have : 4 * m < k ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_right this (by linarith)
  have h2 : k ^ 2 * t ≤ t * t := mul_le_mul_of_nonneg_right hkt (by linarith)
  have hs : 625 ≤ t * t := by nlinarith
  have h3 : t * t + 1 < t ^ 4 := by
    have e4 : t ^ 4 = t * t * (t * t) := by ring
    have := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ t * t)
    nlinarith
  linarith

theorem bound_of_over (K : Ctx) (B : Pre) (h : K.Over B) (i : Fin 2) :
    4 * (B.R.m : ℝ) * (B.host.g i : ℝ) ^ ((1 : ℝ) / 4) < (B.host.g i : ℝ) - 1 := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  show 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) < (K.P.H.g i : ℝ) - 1
  have hr : RankVal K.s K.P.R := K.ok.rank
  unfold RankVal at hr
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hr
  have hv : HostVal K.s K.C.P.Cpde K.P.H := K.ok.val
  unfold HostVal at hv
  obtain ⟨-, -, -, -, hg, -⟩ := hv
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have he0 : 0 < K.s.eps := K.s.eps_pos
  have hx0 : (0 : ℝ) ≤ K.s.x := by linarith
  have hd1 : K.s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 : 0 ≤ K.s.delta1 := Real.rpow_nonneg hx0 _
  set y := Real.sqrt K.s.x with hy
  have hy2 : y ^ 2 = K.s.x := Real.sq_sqrt hx0
  have hy1 : 1 ≤ y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1.le
  have hmy : (K.P.R.m : ℝ) ≤ 2 * y := by
    have : Real.sqrt (K.s.x * K.s.delta1) ≤ y := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hk4 : K.s.x ^ (4 : ℕ) ≤ (K.P.R.k : ℝ) := by
    have h1 : K.s.x ^ (4 : ℝ) ≤ K.s.x ^ ((9 : ℝ) / 2 + 10 * K.s.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h2 : K.s.x ^ (4 : ℝ) = K.s.x ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast K.s.x 4
    exact le_trans (le_trans h2.symm.le h1) hk
  have hk8 : y ^ 8 ≤ (K.P.R.k : ℝ) := by
    have : y ^ 8 = K.s.x ^ (4 : ℕ) := by rw [← hy2]; ring
    linarith
  have hk2 : (2 : ℝ) ≤ K.P.R.k := by
    have h1 : (1 : ℝ) < K.P.R.k := lt_of_lt_of_le (one_lt_pow₀ hx1 (by norm_num)) hk4
    have h2 : 1 < K.P.R.k := by exact_mod_cast h1
    exact_mod_cast h2
  have hb : (2.718 : ℝ) ≤ K.s.b := by
    have hL : 1 ≤ K.s.L := Real.one_le_rpow hx1.le he0.le
    have h1 : Real.exp 1 ≤ K.s.b := Real.exp_le_exp.2 hL
    have h2 := Real.exp_one_gt_d9
    linarith
  have hkb1 : (5 : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
  have hkb2 : 2 * y + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have hkb : 2.718 * (K.P.R.k : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
    by_cases h5 : (5 : ℝ) ≤ (K.P.R.k : ℝ)
    · have : y ≤ y ^ 8 := le_self_pow₀ hy1 (by norm_num)
      linarith
    · push_neg at h5
      have hk4' : (K.P.R.k : ℝ) ≤ 4 := by
        have : K.P.R.k < 5 := by exact_mod_cast h5
        have : K.P.R.k ≤ 4 := by omega
        exact_mod_cast this
      have hy12 : y ≤ 1.2 := by
        by_contra hc
        push_neg at hc
        have : (1.2 : ℝ) ^ 8 < y ^ 8 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
        norm_num at this
        linarith
      linarith
  have hM : max 2 (K.P.R.m : ℝ) + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have : max 2 (K.P.R.m : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b - 3 := max_le (by linarith) (by linarith)
    linarith
  have hmain := four_mul_root_lt (le_max_left 2 (K.P.R.m : ℝ)) hM (hg i).1
  have ht : (0 : ℝ) ≤ (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hle : 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) ≤
      4 * max 2 (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := by
    have : (K.P.R.m : ℝ) ≤ max 2 (K.P.R.m : ℝ) := le_max_right _ _
    nlinarith
  linarith

theorem tame_of_pow : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧ ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) → ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩; DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
  have key : ∀ K : Ctx, ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k),
      ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
        ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) →
      ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩;
        DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
    intro K X hO hpow k v
    obtain ⟨w, hw, hchi⟩ := hpow k v
    have hb := bound_of_over K X.B.toPre hO k
    have hr : 1 ≤ X.toD7.R.r := by
      have h2 := X.toD7.R.two_le_m
      first
      | (show 1 ≤ X.toD7.R.k + X.toD7.R.m - 1; omega)
      | omega
      | (simp only [Formalism.MainNotions.Ranks.r]; omega)
      | (unfold Formalism.MainNotions.Ranks.r; omega)
    have e : X.toD7.nd.chiT k v = fun j : Fin X.B.R.m => w ^ (2 * (j.1 + 1)) := funext hchi
    haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩
    have h := GlobalTheory.EX.DC.TameGen.tameDistinct_gen X.toD7.R.r (X.toD7.host.g k) X.B.R.m w hw hb hr
    rw [e]
    exact h
  unfold Ev
  refine ⟨1, one_pos, ?_⟩
  intro eps C8 _ _ _ _
  refine ⟨?k0, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K => ?_⟩⟩⟩⟩
  case k0 => first | exact ⟨0, 0, 0, 0⟩ | exact default | exact Classical.arbitrary _
  first
  | exact key K
  | exact fun _ => key K
  | exact fun _ _ => key K
  | exact fun _ _ _ => key K
  | exact fun _ _ _ _ => key K
  | exact fun _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ _ => key K

end GlobalTheory.Mem.Top.TamePow
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TwFin

theorem exists_over {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremFour.main
  | exact _root_.GlobalTheory.IsolatedTheoremFour.main
  | (apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremFour.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremFour.main ..)

theorem finite_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact hv

theorem mul_ne_one {R : Ranks} {H : Formalism.BasicNotions.Host R} {S : Set ℕ} {p : ℕ} {δ ψ : HChar H.E} (hp : p.Prime) (hS : p ∈ S)
    (hδ : IsDelta (H := H) p δ) (hψ : Chr.IsTwist H S ψ) : δ * ψ ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_over (K := H.E) hp
  have hu : ψ.UnrAt v := by
    by_contra hn
    obtain ⟨-, hq, -, hnS⟩ := hψ.2.2.2 v hn
    have := Examples₂.PlacesToy.prime_mem_unique v hq hp (Ideal.absNorm_mem _) hv
    exact hnS (this ▸ hS)
  have h1 := (hδ.ine v hv 1).1 fun x hx => by
    have h2 : (δ * ψ).loc v x = 1 := by
      rw [h]
      rfl
    change δ.loc v x * ψ.loc v x = 1 at h2
    rw [hu x hx, mul_one] at h2
    simpa only [pow_one] using h2
  omega

theorem resChar_conj (B : Base) (w : B.places.Pl) : B.places.resChar (B.places.conj w) = B.places.resChar w := by
  refine Examples₂.PlacesToy.prime_mem_unique (B.places.conj w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) ?_
  have h := (Examples₂.PlacesToy.mem_conjW_pow w ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) 1).2
    (by rw [pow_one, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)
  rw [pow_one] at h
  exact h

theorem finite_pl (B : Base) (s : Finset ℕ) : {w : B.places.Pl | B.places.resChar w ∈ s}.Finite := by
  refine ((s.finite_toSet.subset (s := (s : Set ℕ)) (t := {p | p ∈ s ∧ p ≠ 0}) fun p hp => hp.1).biUnion
    fun p hp => finite_mem (K := B.LL) hp.2).subset fun w hw => ?_
  simp only [Set.mem_iUnion]
  exact ⟨B.places.resChar w, ⟨hw, (B.places.resChar_prime w).ne_zero⟩, Examples₂.PlacesToy.resCharW_mem w⟩

theorem tw_fin : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B), (T.set f).Finite ∧ (∀ w, T.xiTw f w ≠ 1) ∧ (∀ w, T.xiTw f (B.places.conj w) = T.xiTw f w) ∧ {w : B.places.Pl | B.places.resChar w ∈ T.pl}.Finite := by
  intro B f T
  refine ⟨?_, fun w => ?_, fun w => ?_, finite_pl B T.pl⟩
  · have h3 : ({1, f.del, f.del'} : Set (HChar B.host.E)).Finite := Set.toFinite _
    refine (h3.union ((finite_pl B T.pl).image (T.xiTw f))).subset ?_
    rintro ξ (h | ⟨w, rfl⟩)
    · exact Or.inl h
    · by_cases hw : B.places.resChar w ∈ T.pl
      · exact Or.inr ⟨w, hw, rfl⟩
      · left
        unfold TwDat.xiTw
        rw [(T.off w hw).1, mul_one]
        split_ifs
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
  · unfold TwDat.xiTw
    split_ifs
    · exact mul_ne_one B.host.pde'_prime (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) f.isDel' (T.psi_tw w)
    · exact mul_ne_one B.host.pde_prime (Or.inr (Or.inr (Or.inl rfl))) f.isDel (T.psi_tw w)
  · unfold TwDat.xiTw
    rw [resChar_conj, (T.conj w).1]

end GlobalTheory.Mem.Top.TwFin
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem exists_locComp_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsAdmissible σ.ρ ∧ π.IsLocComp w σ ∧ (IsUnramU π.V w ↔ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := n))) := by
  intro E _ _ _ n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hsym : ∀ x : locU n w, e.symm (cLoc w (x : UA E n)) = x := fun x => by
    rw [← he, e.symm_apply_apply]
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) σ₀.V :=
    σ₀.ρ.comp e.symm.toMulEquiv.toMonoidHom
  have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
  let σ : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
    { V := σ₀.V
      ρ := ρ
      smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
      irred := GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ₀.ρ e.symm.toMulEquiv σ₀.irred }
  have hf' : ∀ (x : locU n w) v, f (σ₀.ρ x v) = RU E n x (f v) := hf
  refine ⟨σ, GlobalTheory.CuspMult.isAdmissible_comp_equiv σ₀.ρ e.symm hadm, ⟨σ.irred, f, hf0, hfm, fun x v => ?_⟩, ?_, ?_⟩
  · change f (ρ (cLoc w (x : UA E n)) v) = _
    rw [hρ, hsym, hf']
  · rintro ⟨φ, hφ, h0, hK⟩
    let F : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hsup := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ₀.V σ₀.V π.rep (locU n w).subtype σ₀.ρ σ₀.ρ
      π.isIrreducible_rep σ₀.irred σ₀.irred (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ₀.ρ σ₀.irred
      (fun h : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
      (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
      {k | cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hK k k.2 hk))
      (hsup ▸ Submodule.mem_top)
    intro hb
    have hmem : v ∈ fixed ρ (GlobalTheory.LFun.KGL w (n := n)) := fun g => by
      have h1 : σ₀.ρ (e.symm g.1) v = v := hv _ (by
        have h2 : cLoc w ((e.symm g.1 : locU n w) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
          rw [hcl]
          exact g.2
        exact h2)
      simpa [hρ] using h1
    have hb' : fixed ρ (GlobalTheory.LFun.KGL w (n := n)) = ⊥ := hb
    rw [hb'] at hmem
    exact hv0 ((Submodule.mem_bot _).1 hmem)
  · intro hsph
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hinj : Function.Injective f := by
      have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ₀.irred).2 (LinearMap.ker f) (fun g u hu => by
        rw [LinearMap.mem_ker] at hu ⊢
        rw [hf', hu, map_zero])
      rcases hk with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · exact absurd (LinearMap.ker_eq_top.1 h) hf0
    refine ⟨f v, hfm v, fun h => hv0 (hinj (h.trans (map_zero f).symm)), fun x hx hk => ?_⟩
    have h1 : σ₀.ρ (⟨x, hx⟩ : locU n w) v = v := by
      have h2 : ρ (cLoc w x) v = v := by simpa using hv ⟨_, hk⟩
      rwa [hρ, hsym (⟨x, hx⟩ : locU n w)] at h2
    have h3 := hf' ⟨x, hx⟩ v
    rw [h1] at h3
    exact h3.symm

end GlobalTheory.DefU
end
end
