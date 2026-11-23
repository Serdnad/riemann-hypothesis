module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Finset

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem prod_lamCfg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Y : ℝ) : ∏ s, (Y + lamCfg S v s) = S.P v Y := by
  show ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) = (S.G.place (S.pl v)).P Y
  have hm : (S.G.place (S.pl v)).k + (S.G.place (S.pl v)).m - 1 =
      (D.parOf S v).k + 2 * (D.parOf S v).r + 1 := by
    show S.G.k + (2 * S.G.r + 2) - 1 = S.G.k + 2 * S.G.r + 1
    omega
  rw [Sz.Cfg.P, hm]
  have e1 : ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) =
      ∏ i ∈ Finset.range ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
        (Y + (S.G.place (S.pl v)).lam (i + 1)) :=
    Fin.prod_univ_eq_prod_range (fun i => Y + (S.G.place (S.pl v)).lam (i + 1)) _
  rw [e1, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => Y + (S.G.place (S.pl v)).lam i), zero_add]
  rfl

theorem level_system_admissible_size (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (hA : D.AdmAt S v a)
    (hI : ∀ x ∈ a, x.2 ∈ Set.Icc (S.cutLo v) (S.cutHi v)) (l : ℕ)
    (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT) (c : LE.Cut) (Lb : ℝ) :
    (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).admitted a ∧
      (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).size a = S.sizeAt v a := by
  obtain ⟨w, rfl⟩ := hA
  refine ⟨⟨fun x hx => hI x hx, ?_⟩, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i i' hi hi' hii
    have := w.2.1.2 v i i' hi hi' (Nat.ne_of_lt hii) 0 (by norm_num) (by norm_num)
    simpa using this
  · show ((w.1 v).map fun x => |∏ s, (x.2 + lamCfg S v s)|).prod = _
    rw [C.HidaSetting.sizeAt]
    simp only [prod_lamCfg]

end defs

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

section cfg

variable (c : Sz.Cfg)

theorem cfg_v_sub (i : ℕ) : c.v i - c.v (i + 1) = 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring

theorem cfg_v_ge_vlast (hok : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i := by
  have hD := hok.hDel
  have hi' : (i : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hi
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_v_lt (hok : c.Ok) {i j : ℕ} (hij : i < j) : c.v j < c.v i := by
  have hD := hok.hDel
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_b_lt (hok : c.Ok) : ∀ {j j' : ℕ}, 1 ≤ j → j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j j' hj hjj' hj'm
  induction j' with
  | zero => omega
  | succ n ih =>
    have hg := hok.hgap n (by omega) (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjj' with h | h
    · have := ih h (by omega)
      linarith
    · subst h
      linarith

theorem cfg_b_ge_one (hok : c.Ok) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.lt_or_ge 1 j with h | h
  · have := cfg_b_lt c hok (le_refl 1) h hjm
    linarith [hok.hb1]
  · have e : j = 1 := by omega
    subst e
    exact hok.hb1

theorem cfg_interlaces (r : ℕ) (hm : c.m = 2 * r + 2) (hk : 2 ≤ c.k) (hok : c.Ok) (de : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) :
    C7.LamInterlaces c.k r (c.u de) (fun s : Fin (c.k + 2 * r + 1) => c.lam ((s : ℕ) + 1)) := by
  have hk4 := hok.hk
  have hD := hok.hDel
  have hv0 := hok.hv0
  have hb1 := hok.hb1
  have ha := hok.ha
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlamv : ∀ s : ℕ, s < c.k → c.lam s = c.v s := fun s hs => by
    rw [Sz.Cfg.lam, if_pos hs]
  have hlamb : ∀ s : ℕ, ¬ s < c.k → c.lam s = -c.b (s + 1 - c.k) := fun s hs => by
    rw [Sz.Cfg.lam, if_neg hs]
  have hu1 : c.u de 1 = c.a := by rw [Sz.Cfg.u, if_pos rfl]
  have huk : c.u de c.k = c.ulast := by rw [Sz.Cfg.u, if_neg (by omega), if_pos rfl]
  have hum : ∀ j : ℕ, j ≠ 1 → j ≠ c.k → c.u de j = c.v (j - 1) - 1 / 2 - de (j - 1) * c.Del :=
    fun j h1 h2 => by rw [Sz.Cfg.u, if_neg h1, if_neg h2]
  have hde0 : ∀ j, 0 ≤ de j * c.Del ∧ de j * c.Del ≤ c.Del := fun j => by
    rcases hde j with h | h <;> simp [h] <;> linarith
  have hul : c.ulast = if c.top then -c.bp else c.vlast - 1 / 2 := rfl
  have hvk : c.v (c.k - 1) = c.vlast := by
    simp only [Sz.Cfg.v]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  refine ⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro s t hst
    show c.lam ((t : ℕ) + 1) < c.lam ((s : ℕ) + 1)
    by_cases h1 : (t : ℕ) + 1 < c.k
    · rw [hlamv _ h1, hlamv _ (by omega)]
      exact cfg_v_lt c hok (by omega)
    · rw [hlamb _ h1]
      by_cases h2 : (s : ℕ) + 1 < c.k
      · rw [hlamv _ h2]
        have := cfg_b_ge_one c hok (j := (t : ℕ) + 1 + 1 - c.k) (by omega) (by omega)
        have := cfg_v_ge_vlast c hok ((s : ℕ) + 1) (by omega)
        linarith
      · rw [hlamb _ h2]
        have := cfg_b_lt c hok (j := (s : ℕ) + 1 + 1 - c.k) (j' := (t : ℕ) + 1 + 1 - c.k)
          (by omega) (by omega) (by omega)
        linarith
  · show c.lam ((i : ℕ) + 1) < c.u de ((i : ℕ) + 1)
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, zero_add, hlamv 1 (by omega), hu1]
      have : 0 < 4 * (c.k : ℝ) * c.Del := by
        have := mul_le_mul hkR hD zero_le_one (by linarith)
        linarith
      linarith
    · by_cases h2 : (i : ℕ) + 1 < c.k
      · rw [hlamv _ h2, hum _ (by omega) (by omega), Nat.add_sub_cancel]
        have := cfg_v_sub c (i : ℕ)
        have := hde0 (i : ℕ)
        linarith
      · have e : (i : ℕ) + 1 = c.k := by omega
        rw [hlamb _ h2, e, Nat.add_sub_cancel_left, huk, hul]
        split_ifs with htp
        · have := (hok.htop htp).2
          linarith
        · linarith
  · show c.u de ((i : ℕ) + 2) < c.lam ((i : ℕ) + 1)
    rw [hlamv _ (by omega)]
    by_cases h2 : (i : ℕ) + 2 = c.k
    · have e : (i : ℕ) + 1 = c.k - 1 := by omega
      rw [h2, huk, hul, e, hvk]
      split_ifs with htp
      · have := (hok.htop htp).1
        linarith
      · linarith
    · have e : (i : ℕ) + 2 - 1 = (i : ℕ) + 1 := by omega
      rw [hum _ (by omega) h2, e]
      have := hde0 ((i : ℕ) + 1)
      linarith

end cfg

theorem eigenvalue_configuration_interlaces : LamCfgInterlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S hk hok hw hw' v
  exact ⟨cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de hw.1,
    cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de' hw'.1⟩

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuiltPlace_mono {Cc₁ Cc₂ : ℝ} (h : Cc₁ ≤ Cc₂) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ : ℝ} (hB : JCT.IsBuiltPlace Cc₂ S T f χ ν' m₀ top A₀) : JCT.IsBuiltPlace Cc₁ S T f χ ν' m₀ top A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hB
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun v => le_trans ?_ (h8 v), le_trans h h9, h10, h11, le_trans ?_ h12, h13⟩
  · exact mul_le_mul_of_nonneg_right h (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)

theorem toSm_smul (P : M.Par) (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) : MA.toSm P (c • u) = c • MA.toSm P u := by
  unfold Formalism.FourierDecayAlt.MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [dite_eq_left hu, dite_eq_left (Subalgebra.smul_mem _ hu c)]
    rfl
  · rw [dite_eq_right hu, smul_zero]
    by_cases hc : c = 0
    · subst hc
      rw [dite_eq_left (by rw [zero_smul]; exact Subalgebra.zero_mem _)]
      exact Subtype.ext (by simp)
    · rw [dite_eq_right]
      intro h
      apply hu
      have h2 := Subalgebra.smul_mem _ h c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem hsVec_smul {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (c : ℂ) (A : W →L[ℂ] V) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rfl

theorem trJ_smul (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (c : ℂ) (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    trJ S T v e (c • J) = c • trJ S T v e J := by
  funext ρ
  simp only [trJ, Pi.smul_apply, hsVec_smul, inner_smul_right]
  rw [← toSm_smul]
  congr 1
  funext q
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem trJ_congr (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (J J' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (h : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, J (B.gq (T v).base x) = J' (B.gq (T v).base x)) :
    trJ S T v e J = trJ S T v e J' := by
  funext ρ
  simp only [trJ]
  congr 1
  funext q
  rw [h q.1 q.2]

def prFst (P : M.Par) : (MA.DQ P).Pr →+ (MA.DQ P).Op where
  toFun p := p.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pr_fst_sum (P : M.Par) {ι : Type} (s : Finset ι) (g : ι → (MA.DQ P).Pr) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  exact map_sum (prFst P) g s

theorem pr_fst_smul (P : M.Par) (c : ℂ) (a : (MA.DQ P).Pr) : (c • a).1 = c • a.1 := by
  rfl

theorem op_sum_apply (P : M.Par) {ι : Type} (s : Finset ι) (g : ι → (MA.DQ P).Op) (y : (MA.DQ P).R) :
    (∑ i ∈ s, g i) y = ∑ i ∈ s, g i y := by
  first
  | exact LinearMap.sum_apply s g y
  | exact ContinuousLinearMap.sum_apply s g y
  | simp

theorem actA_mul (P : M.Par) (a b : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (a * b) x = MA.actA P a (MA.actA P b x) := by
  funext π
  show ∑ π', ((a * b) π π').1 (x π') = ∑ σ, (a π σ).1 (∑ π', (b σ π').1 (x π'))
  have e : ∀ π', ((a * b) π π').1 (x π') = ∑ i, (a π i).1 ((b i π').1 (x π')) := by
    intro π'
    rw [Matrix.mul_apply, pr_fst_sum]
    first
      | exact (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | exact (ContinuousLinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | exact (op_sum_apply P Finset.univ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | (simp; rfl)
  rw [Finset.sum_congr rfl fun π' _ => e π', Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_

  rw [map_sum]

theorem actA_smul (P : M.Par) (c : ℂ) (a : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • a) x = c • MA.actA P a x := by
  funext π
  simp only [Formalism.FourierDecayAlt.MA.actA, Matrix.smul_apply, pr_fst_smul, Pi.smul_apply]
  rw [eq_comm]
  erw [Finset.smul_sum]
  symm
  refine Finset.sum_congr rfl fun π' _ => ?_
  first
    | exact LinearMap.smul_apply _ _ _
    | exact ContinuousLinearMap.smul_apply _ _ _
    | rfl

theorem actA_one (P : M.Par) (x : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 x = x := by
  classical
  funext π
  simp only [Formalism.FourierDecayAlt.MA.actA, Matrix.one_apply]
  erw [Finset.sum_eq_single π (fun b _ hb => by simp only [if_neg (Ne.symm hb)]; rfl)
    (fun h => absurd (Finset.mem_univ π) h)]
  simp only [if_pos rfl]
  rfl

theorem initial_coefficient_of_start_matrix (P : M.Par) (l : ℕ) (Y : ℂ) :
    Wd.C0 (MA.startM P (MA.DQ P) l).QQ (MA.sites P (MA.DQ P)) Y =
      M.sgn P l • Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) Y := by
  simp only [Formalism.FourierDecayAlt.Wd.C0, Formalism.FourierDecayAlt.MA.startM, Matrix.smul_apply, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum]

end asm

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem trJ_foldr (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hG : IsGauge S T v e)
    (hP : ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) :
    ∀ (L : List (Bool × ℝ)) (J₀ : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), J₀ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      L.foldr (fun x J => M.sgn (D.parOf S v) (S.l + 1) • Q.CV S.G.k S.G.r (x.2 : ℂ) J) J₀ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
      trJ S T v e (L.foldr (fun x J => M.sgn (D.parOf S v) (S.l + 1) • Q.CV S.G.k S.G.r (x.2 : ℂ) J) J₀) =
        MA.actA (D.parOf S v) ((L.map fun x => Wd.C0 (MA.startM (D.parOf S v) (MA.DQ (D.parOf S v)) (S.l + 1)).QQ
          (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (x.2 : ℂ)).prod) (trJ S T v e J₀) := by
  intro L J₀ hJ₀
  induction L with
  | nil =>
    refine ⟨hJ₀, ?_⟩
    simp only [List.foldr_nil, List.map_nil, List.prod_nil]
    rw [actA_one]
  | cons x L ih =>
    obtain ⟨hmem, htr⟩ := ih
    refine ⟨hP _ hmem x.2 _, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [trJ_smul, hG _ hmem x.2, ← actA_smul, ← initial_coefficient_of_start_matrix, htr, ← actA_mul]

end main

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def GermOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq),
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r →
        B.opApply Θ f g = B.opApply Θ f' g ∧ B.opAdj Θ f g = B.opAdj Θ f' g) ∧
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r),
      B.opApply Θ (c • f) g = c • B.opApply Θ f g ∧ B.opAdj Θ (c • f) g = c • B.opAdj Θ f g)

def ExtLoc : Prop :=
  ∀ (k r : ℕ) (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (O : Set (B.Mat k r)) (J : B.Mat k r → E'),
    IsOpen O → Q.SmoothLev k r 0 O J → ∀ g₀ ∈ B.GV k r, g₀ ∈ O →
      ∃ (f : B.Mat k r → E') (U : Set (B.Mat k r)), B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧
        IsOpen U ∧ g₀ ∈ U ∧ ∀ x ∈ U, x ∈ B.GV k r → f x = J x

def SmoothOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (O : Set (B.Mat k r)), IsOpen O → (∀ g ∈ O, g ∈ B.GV k r → g ∈ B.GPos D) →
    B.SmoothCoef (B.GPos D) Θ → ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O →
      Q.SmoothLev k r 0 O (B.opApply Θ f) ∧ Q.SmoothLev k r 0 O (B.opAdj Θ f)

def AdjComm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ g ∈ B.GPos D, B.opAdj Θ (B.rho D p f) g = B.rho D p (B.opAdj Θ f) g

def EquivOps : Prop :=
  ExtLoc →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (O : Set (B.Mat k r)) (P : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsDom k r D.z D.z' 0 O →
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r → P f g = P f' g) →
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → P (c • f) g = c • P f g) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O → Q.SmoothLev k r 0 O (P f)) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → tsupport f ⊆ O →
      ∀ p, D.inSS p → ∀ g ∈ O, g ∈ B.GV k r → P (B.rho D p f) g = B.rho D p (P f) g) →
    ∀ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O, P J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O

def OmPDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f),
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) ∧
      ∀ g ∈ OmP S T v, g ∈ B.GV S.G.k S.G.r → g ∈ B.GPos (T v).base

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end
