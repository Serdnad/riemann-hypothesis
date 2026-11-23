module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyPsiWithExceptionalZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle075
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.Padics.ProperSpace
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

section Inputs

open Formalism.MainNotions.TaylorLogMetric

def goodLifts (D : D7) (T : Tor D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AddSubgroup (VC D N N') :=
  AddSubgroup.closure {y | ∃ κ : 𝓞 D.host.K,
    ‖lamC lam (D.host.φ₀ (D.host.conj ((κ : D.host.K) : D.host.E)))‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
    ∃ x ∈ La D T L L', y = (D.host.φ₀ ((κ : D.host.K) : D.host.E) * (N₀ : ℂ) / (p : ℂ) ^ n) • x}

def MomentsAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (Ω : ℂ_[p]) : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D p (La D (tor0 D cc δ) L L') t →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D (tor0 D cc δ) δ p L L' b →
    ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
      ∀ (n : ℕ), ∀ y ∈ goodLifts D (tor0 D cc δ) lam N₀ n L L',
        CoefIn D (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L'))) Qbar ∧
        ∀ (m : ℕ) (y' : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a : Fin r → ℕ, g (fun i => (a i : ℤ_[p])) =
            lamC lam (kap D (tor0 D cc δ) (δ • embV D (tor0 D cc δ) (∑ i, (a i : D.host.E) • b i)) y) *
              ∏ j, pairN D lam Ω b (y' j) fun i => (a i : ℤ_[p])) →
          jet D lam y' (pSer D lam (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L')))) = μ g

def MovesAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ

def LatticeFactsAll : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ →
    ∀ a b : ℕ, Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b

end Inputs

section Ops

variable {X : Fields} (A : Amb X) {a b : ℕ}

def emb (x : HomE X.E a b) : VCx X.Tau a b := embH (X.embC A.σ₀) A.δ x

def Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) : VCx X.Tau a b → ℂ :=
  fun z => alV A.d A.sc (emb A x) * opU (HV A.sc) (emb A x) F z

def imH (x y : HomE X.E a b) : ℝ := altE (HV A.sc) (emb A x) (emb A y)

def coc (x y : HomE X.E a b) : ℝ := (Real.sqrt A.d * (HV A.sc (emb A x) (emb A y)).re + imH A x y) / 2

def brkE (y t : HomE X.E a b) : ℂ := brk (HV A.sc) (emb A y) (emb A t)

abbrev per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  perO A.AA N N'

def smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  M.map ((r • (LinearMap.id : HomE X.E a b →ₗ[X.E] HomE X.E a b)).restrictScalars (𝓞 X.E))

theorem mem_smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) (y : HomE X.E a b) :
    y ∈ smulLat r M ↔ ∃ m ∈ M, r • m = y := Iff.rfl


variable (a b) in
def PtMom {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (v : X.E) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ t : HomE X.E a b, (∃ n : ℕ, Nat.Coprime n p ∧ (n : X.E) • t ∈ per A N N') →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
      (∀ y ∈ per A N N', ∀ m, jetC A.cD (Wx A (((N₀ : X.E) * v) • y) (Wx A t (A.e a b N N'))) m ∈ TaylorLogMetric.Qbar) ∧
      InIntClosure (per A N N' : Set (HomE X.E a b))
        (fun x (k : HomE X.E a b × (DVar X.Tau a b →₀ ℕ)) =>
          TaylorLogMetric.lamC lam (brkE A (((N₀ : X.E) * v) • k.1) x) * ptTab ι un x k.2)
        {k | k.1 ∈ per A N N'}
        fun k => TaylorLogMetric.lamC lam (jetC A.cD (Wx A (((N₀ : X.E) * v) • k.1) (Wx A t (A.e a b N N'))) k.2)


variable (a b) in
def Ctx (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AAUnit (divs (X.conjO ϖ)) ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧
    IsCoprime ϖ (X.conjO ϖ) ∧ (∀ P, P ∈ S ↔ ϖ ∈ P.asIdeal ∨ P ∈ SG) ∧ (∀ P ∈ SG, (p : 𝓞 X.E) ∉ P.asIdeal) ∧
    Nat.Coprime g p ∧ Nat.Coprime cA p

end Ops

section Clo

variable {p : ℕ} [Fact p.Prime] {H I : Type}

theorem clo_zero (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) : InIntClosure Sup tab M fun _ => 0 := by
  intro F _ ε hε
  exact ⟨0, by simp, by simp, by simpa using fun _ _ => hε⟩

theorem clo_add {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (h' : InIntClosure Sup tab M J') : InIntClosure Sup tab M fun m => J m + J' m := by
  classical
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F hF ε hε
  obtain ⟨c', hc', hc1', hcF'⟩ := h' F hF ε hε
  refine ⟨c + c', ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_add (Finset.mem_coe.1 hx)) with h | h
    exacts [hc h, hc' h]
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc1 x) (hc1' x))
  · rw [Finsupp.sum_add_index' (by simp) (by intros; ring)]
    have : J m + J' m - ((c.sum fun x r => r * tab x m) + c'.sum fun x r => r * tab x m) =
        (J m - c.sum fun x r => r * tab x m) + (J' m - c'.sum fun x r => r * tab x m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hcF m hm) (hcF' m hm))

theorem clo_sum {κ : Type} {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} (s : Finset κ) (J : κ → I → ℂ_[p])
    (h : ∀ k ∈ s, InIntClosure Sup tab M (J k)) : InIntClosure Sup tab M fun m => ∑ k ∈ s, J k m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using clo_zero Sup tab M
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact clo_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem clo_congr {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {M M' : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (hS : Sup ⊆ Sup') (hM : M' ⊆ M) (hJ : ∀ m ∈ M', J' m = J m) :
    InIntClosure Sup' tab M' J' := by
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F (hF.trans hM) ε hε
  exact ⟨c, hc.trans hS, hc1, fun m hm => by rw [hJ m (hF hm)]; exact hcF m hm⟩

theorem clo_comb {I' κ : Type} {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {tab' : H → I' → ℂ_[p]} {M : Set I} {M' : Set I'}
    {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J) (s : Finset κ) (r : κ → I' → ℂ_[p]) (φ : κ → I' → I)
    (hφ : ∀ k ∈ s, ∀ m ∈ M', φ k m ∈ M) (w : H → ℂ_[p]) (hw : ∀ x ∈ Sup, ‖w x‖ ≤ 1) (hw0 : ∀ x ∈ Sup, x ∉ Sup' → w x = 0)
    (htab : ∀ x ∈ Sup, ∀ m ∈ M', ∑ k ∈ s, r k m * tab x (φ k m) = w x * tab' x m) :
    InIntClosure Sup' tab' M' fun m => ∑ k ∈ s, r k m * J (φ k m) := by
  classical
  intro F hF ε hε
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ k ∈ s, ∀ m ∈ F, ‖r k m‖ ≤ C := by
    refine ⟨1 + ∑ q ∈ s ×ˢ F, ‖r q.1 q.2‖, by positivity, fun k hk m hm => ?_⟩
    have := Finset.single_le_sum (f := fun q : κ × I' => ‖r q.1 q.2‖) (fun _ _ => norm_nonneg _)
      (Finset.mk_mem_product hk hm)
    linarith
  obtain ⟨c, hc, hc1, hcF⟩ := h ((s ×ˢ F).image fun q => φ q.1 q.2) (by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
    exact hφ _ (Finset.mem_product.1 hq).1 _ (hF (Finset.mem_product.1 hq).2)) (ε / 2 / C) (by positivity)
  have hmem : ∀ x, c x ≠ 0 → x ∈ Sup := fun x hx => hc (Finsupp.mem_support_iff.2 hx)
  refine ⟨Finsupp.onFinset c.support (fun x => c x * w x) (fun x hx => Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hx)),
    ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    have hx' : c x * w x ≠ 0 := by simpa using hx
    by_contra hn
    exact hx' (by rw [hw0 x (hmem x (left_ne_zero_of_mul hx')) hn, mul_zero])
  · rw [Finsupp.onFinset_apply]
    by_cases hx : c x = 0
    · simp [hx]
    · rw [norm_mul]; exact mul_le_one₀ (hc1 x) (norm_nonneg _) (hw x (hmem x hx))
  · rw [Finsupp.onFinset_sum _ (by simp)]
    have e : ∑ k ∈ s, r k m * J (φ k m) - ∑ x ∈ c.support, c x * w x * tab' x m =
        ∑ k ∈ s, r k m * (J (φ k m) - c.sum fun x q => q * tab x (φ k m)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finsupp.sum, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mul_assoc, ← htab x (hc hx) m (hF hm), Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := ε / 2) (by positivity) fun k hk => ?_)
      (by linarith)
    rw [norm_mul]
    have h1 := hcF (φ k m) (Finset.mem_image.2 ⟨(k, m), Finset.mk_mem_product hk hm, rfl⟩)
    calc _ ≤ C * (ε / 2 / C) := mul_le_mul (hC k hk m hm) h1.le (norm_nonneg _) hC0.le
      _ = ε / 2 := by field_simp

theorem clo_smul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r c : ℂ_[p]) (hc : c ≠ 0) (hr : ‖r‖ ≤ ‖c‖) :
    InIntClosure Sup (fun x m => c * tab x m) M fun m => r * J m := by
  have := clo_comb (Sup' := Sup) (tab' := fun x m => c * tab x m) (M' := M) h ({()} : Finset Unit) (fun _ _ => r) (fun _ m => m)
    (fun _ _ _ hm => hm) (fun _ => r / c)
    (fun _ _ => by rw [norm_div]; exact div_le_one_of_le₀ hr (norm_nonneg _)) (fun _ h h' => absurd h h')
    (fun x _ m _ => by simp only [Finset.sum_singleton]; field_simp)
  simpa using this

theorem clo_mul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r : ℂ_[p]) (hr : ‖r‖ ≤ 1) : InIntClosure Sup tab M fun m => r * J m := by
  simpa using clo_smul h r 1 one_ne_zero (by simpa using hr)

end Clo

end GlobalTheory.MomT
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rpow_mul_X'_le_b (eps c : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    s.x ^ c * s.X' ≤ s.b ∧ s.x ^ 10 ≤ s.X' := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps c 1 1 0 (by positivity)
    (by linarith) one_pos
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 10 0 1 0 le_rfl
    (by linarith) one_pos
  refine ⟨max x0 x1, fun s hs hx => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h2 := h0 s.x ((le_max_left _ _).trans hx)
  have h3 := h1 s.x ((le_max_right _ _).trans hx)
  rw [← hs] at h2 h3
  simp only [pow_zero, one_mul, mul_one, zero_mul, add_zero] at h2 h3
  constructor
  · rw [Real.rpow_def_of_pos hx0, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · have e : s.x ^ 10 = Real.exp (10 * Real.log s.x) := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X']
    exact Real.exp_le_exp.2 h3

theorem szRow_size_ratio : SzRow (fun C D L => (∀ j j' τ τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m → wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ') ∧ (∀ τ (hm : 0 < D.R.m), (D.hc τ).b ⟨D.R.m - 1, by omega⟩ ≤ 2 * (D.hc τ).b ⟨0, hm⟩)) := by
  intro eps he he' C hC
  obtain ⟨CN, x1, hLa⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, hx2'⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps 1 (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  have hK : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  refine ⟨0, fun cD _ => ⟨0, fun ch hch => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := rpow_mul_X'_le_b eps (ch + 9) he
  refine ⟨max (max x0 x1) (max x2 2), fun D L hs hx hV => ?_⟩
  have hxa : x0 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxb : x1 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxc : x2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hxp : 0 < L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, -⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hX⟩ := hx0 L.sc hs hxa
  have hLa1 : L.LaG ≤ L.sc.x := by
    have h1 := ((hLa L.sc hs hxb).2.2 C.GK hK).2
    have h2 := hx2' L.sc.x hxc
    rw [Real.rpow_one, ← hs] at h2
    rw [hV.La_eq]
    refine h1.trans (le_trans (le_of_eq ?_) h2)
    ring
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 0 < D.R.n := by exact_mod_cast hn0
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k :=
    le_trans (Real.one_le_rpow hx1 (by have := L.sc.eps_pos; linarith)) hV.ranks.2.2.1.1
  have hX0 : 0 < L.sc.X' := Real.exp_pos _
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have eb' : L.sc.b' = L.sc.x * (L.sc.b / L.sc.X') := by rw [Scale.b', Scale.a]; ring
  have ew : L.sc.w'' D.R.n = (L.sc.b / L.sc.X') / D.R.n := by
    rw [Scale.w'', Scale.b', Scale.a]; field_simp
  have hq0 : 0 < L.sc.b / L.sc.X' := div_pos hb0 hX0
  have hb'0 : 0 < L.sc.b' := by rw [eb']; positivity
  have hw0 : 0 < L.sc.w'' D.R.n := by rw [ew]; positivity
  have hwb' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    rw [ew, eb']
    exact (div_le_self hq0.le hn1).trans (le_mul_of_one_le_left hq0.le hx1)
  have h8 : (8 : ℝ) ≤ L.sc.x ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ L.sc.x ^ 3 := by gcongr
    linarith
  have h6 : (1 : ℝ) ≤ L.sc.x ^ 6 := one_le_pow₀ hx1
  have hb'b : 8 * (L.sc.x ^ 6 * L.sc.b') ≤ L.sc.b := by
    have h1 : L.sc.x ^ 10 * (L.sc.b / L.sc.X') ≤ L.sc.X' * (L.sc.b / L.sc.X') := by gcongr
    have h2 : L.sc.X' * (L.sc.b / L.sc.X') = L.sc.b := by field_simp
    rw [eb']
    calc 8 * (L.sc.x ^ 6 * (L.sc.x * (L.sc.b / L.sc.X')))
        ≤ L.sc.x ^ 3 * (L.sc.x ^ 6 * (L.sc.x * (L.sc.b / L.sc.X'))) := by gcongr
      _ = L.sc.x ^ 10 * (L.sc.b / L.sc.X') := by ring
      _ ≤ L.sc.b := h1.trans h2.le
  have hb'6 : L.sc.b' ≤ L.sc.x ^ 6 * L.sc.b' := le_mul_of_one_le_left hb'0.le h6
  have heta : L.etaSz + 1 ≤ L.sc.w'' D.R.n := by
    have hy : 1 ≤ L.sc.x ^ ch := Real.one_le_rpow hx1 hch
    have h1 : (⌈L.sc.x ^ ch⌉₊ : ℝ) ≤ 2 * L.sc.x ^ ch := by
      have := (Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by linarith)).le
      linarith
    have h2 : L.etaSz ≤ L.sc.x ^ 2 * (2 * (2 * L.sc.x ^ ch)) := by
      rw [hV.eta_eq, h0v]
      push_cast
      gcongr
    have h3 : 1 ≤ L.sc.x ^ 2 * L.sc.x ^ ch := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) hy
    have h4 : L.sc.x ^ (ch + 9) = L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch) * L.sc.x ^ 4 := by
      rw [Real.rpow_add hxp, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [ew, le_div_iff₀ hn0, le_div_iff₀ hX0]
    refine le_trans ?_ hb
    rw [h4]
    have h5 : L.etaSz + 1 ≤ 8 * (L.sc.x ^ 2 * L.sc.x ^ ch) := by linarith
    have h7 : 8 * (L.sc.x ^ 2 * L.sc.x ^ ch) ≤ L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch) := by gcongr
    have h9 := h5.trans h7
    have := L.etaSz_pos
    gcongr
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + 2 * (L.sc.x ^ 6 * L.sc.b') := by
    intro t
    refine (hV.bT_le t).trans ?_
    have d1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by have := L.sc.eps_pos; linarith)
    have d0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hxp.le _
    have e1 : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (show L.sc.eps ≤ 1 by have := L.sc.eps_lt; linarith)
      rwa [Real.rpow_one] at this
    have e0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hxp.le _
    have h1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
        2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ) := by gcongr
    have h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ) ≤
        2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' :=
      div_le_self (by positivity) hk1
    have h3 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' ≤
        2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b' := by gcongr
    have h4 : 2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b' = 2 * (L.sc.x ^ 6 * L.sc.b') := by ring
    linarith
  have hd0 : 0 ≤ L.sc.b' / L.sc.x := by positivity
  have hd1 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1
  have hwin : ∀ j τ, 1 ≤ j → j ≤ D.R.m → L.sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b := by
    intro j τ hj hj'
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      obtain ⟨a1, a2⟩ := L.win_top j hj hj' τ ⟨t, htT⟩ hteq.symm
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 := hbT ⟨t, htT⟩
      constructor <;> linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · obtain ⟨a1, a2⟩ := L.win_thick j hj hj' τ h2
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := L.win_thin j hj hj' τ ⟨(D.eTau τ).2, h1, h2⟩
        constructor <;> linarith
  refine ⟨fun j j' τ τ' a1 a2 a3 a4 => ?_, fun τ hm0 => ?_⟩
  · have hXX : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      rw [Scale.X'', div_mul_cancel₀ _ hw0.ne', Scale.a]
    have hXX0 : 0 ≤ L.sc.X'' D.R.n := by
      rw [Scale.X'', Scale.a]; positivity
    calc wj D j τ ≤ 2 * L.sc.b := (hwin j τ a1 a2).2
      _ ≤ L.sc.x * L.sc.b := by gcongr
      _ = L.sc.X'' D.R.n * L.sc.w'' D.R.n := hXX.symm
      _ ≤ L.sc.X'' D.R.n * wj D j' τ' := by gcongr; exact (hwin j' τ' a3 a4).1
  · obtain ⟨-, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
    have hb1 : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
      · classical
        unfold Host.topPlaces at h1
        obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
        rw [htop τ ⟨t, htT⟩ hteq.symm]
        have h2 := L.bT_ge ⟨t, htT⟩
        have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
          exact_mod_cast Int.floor_nonneg.2 hd0
        push_cast
        linarith
      · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
        · have h3 := Int.le_ceil L.sc.b
          have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
          linarith
        · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
          exact Int.le_ceil _
    have h1 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]
      gcongr
      omega
    rw [(hbj τ _).1, (hbj τ _).1, ← Rat.cast_le (K := ℝ)]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_zero,
      zero_mul, add_zero]
    linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), 1 ≤ M → NormOne H.d M p → (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) ∧ p % M = 1 % M := by
  intro R H M p _ h
  obtain ⟨π, hN, hB, hA⟩ := h
  have h' : GlobalTheory.Mem.An.NormOne H.d M p := ⟨π.1, π.2, hN, hB, hA⟩
  exact ⟨(GlobalTheory.Mem.An.normOne_iff_host R H M p).1 h',
    (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd H.d M p (by have := H.hyp.2.2.2.1; omega) h').1⟩

end GlobalTheory.EX
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassFamily_psi_with_exceptional_zero : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ) (u : ℝ), 𝓕.ExcZ χ c₀ Z → 2 ≤ u → Real.log 𝓕.B ≤ Real.sqrt (Real.log u) → ‖𝓕.psi χ u - (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  first | exact @GlobalTheory.Hk.PsiExc.psi_exceptional | exact GlobalTheory.Hk.PsiExc.psi_exceptional | (intros; apply GlobalTheory.Hk.PsiExc.psi_exceptional <;> assumption)
end

section

namespace GlobalTheory.FinitelyGeneratedNatMultiple

theorem exists_nat_smul_mem_of_fg {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (NumberField.RingOfIntegers E) W]
    {M N : Submodule (NumberField.RingOfIntegers E) W}
    (hM : GlobalTheory.ThetaMove.Full M) (hN : Submodule.FG N) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : NumberField.RingOfIntegers E) • x ∈ M := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have hM' : ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : NumberField.RingOfIntegers E) • x ∈ M := hM
  choose n hn0 hn using hM'
  refine ⟨∏ y ∈ s, n y, Finset.prod_pos fun y _ => hn0 y, fun x hx => ?_⟩
  have hle : Submodule.span (NumberField.RingOfIntegers E) (s : Set W) ≤
      M.comap (LinearMap.lsmul (NumberField.RingOfIntegers E) W
        ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E)) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.mp hy)
    show ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E) • y ∈ M
    rw [hk, mul_comm, Nat.cast_mul, mul_smul]
    exact M.smul_mem _ (hn y)
  exact hle hx

end GlobalTheory.FinitelyGeneratedNatMultiple
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.vectors_linearMaps_bounded_denominators_atPrime : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  first | exact @GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | exact GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | (intros; apply GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators <;> assumption)
end
