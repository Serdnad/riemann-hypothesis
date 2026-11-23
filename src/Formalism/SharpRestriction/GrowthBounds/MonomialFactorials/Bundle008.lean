module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.PolynomialDimension.MultinomialDepth.TieOps
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem finrank_zp_le {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (M : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hMW : ∀ x ∈ M, x ∈ W) :
    Module.finrank ℤ_[p] M ≤ Module.finrank ℚ_[p] W := by
  have hr : Module.rank ℤ_[p] M ≤ (Module.finrank ℚ_[p] W : Cardinal) := by
    apply rank_le
    intro s hs
    have h1 : LinearIndependent ℤ_[p] (fun i : s => ((i : M) : V)) :=
      hs.map' M.subtype (Submodule.ker_subtype M)
    have h2 : LinearIndependent ℚ_[p] (fun i : s => ((i : M) : V)) :=
      (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp h1
    have h3 : LinearIndependent ℚ_[p] (fun i : s => (⟨((i : M) : V), hMW _ (i : M).2⟩ : W)) := by
      refine LinearIndependent.of_comp W.subtype ?_
      exact h2
    have := h3.fintype_card_le_finrank
    simpa using this
  exact Module.finrank_le_of_rank_le hr

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)


open Classical in
def xiMons (n : ℕ) : Finset (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) :=
  (CountingStatementReduction.Ev r n).image (fun e => ∑ c : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t c) (e c))

theorem card_xiMons (n : ℕ) : (xiMons (r := r) G n).card ≤ dXi r n := by
  classical
  unfold xiMons
  refine (Finset.card_image_le).trans ?_
  rw [CountingStatementReduction.card_Ev]
  unfold dXi
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e1 : r' + 1 + n - 1 = n + r' := by omega
  have e2 : n + (r' + 1) - 1 = n + r' := by omega
  rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]

theorem xiVar_inj : Function.Injective (Formalism.GM.M.xiVar N r G.T.t) := by
  intro c d h
  simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

theorem xi_mem_span (n : ℕ) (g : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ Formalism.GM.M.XiPolZ p N r G.T.t n) :
    g ∈ Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]))) '' (xiMons (r := r) G n : Set _)) := by
  classical
  have hs := (Submodule.mem_inf.1 hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hs
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' := hs hm
  obtain ⟨hsupp, hsum⟩ := hm'
  have hmono : monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : ℚ_[p]) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
  unfold xiMons
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨fun c => m (Formalism.GM.M.xiVar N r G.T.t c), (CountingStatementReduction.mem_Ev _).2 hsum, ?_⟩
  ext v
  rw [Finsupp.finsetSum_apply]
  by_cases hv : ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c
  · obtain ⟨c, rfl⟩ := hv
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  · have h0 : m v = 0 := by
      by_contra hne
      exact hv (hsupp v (Finsupp.mem_support_iff.2 hne))
    rw [h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hv ⟨c, h.symm⟩

theorem finrank_Ljj_le (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hsub : ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
    intro x hx
    have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
      unfold Ljj
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, g, hg, rfl⟩
      have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
      have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
        rw [← bY.span_eq] at h3
        have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact h4
      have hg2 := xi_mem_span p G (G.B - jp) g hg
      show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
      have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
          (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
          MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hmul := Submodule.mul_mem_mul hy3 hg2
      rw [Submodule.span_mul_span] at hmul
      refine Submodule.span_mono ?_ hmul
      rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨(a, ⟨m, hm⟩), rfl⟩
    exact hle hx
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have h1 := finrank_zp_le (Ljj p (r := r) G j jp) W hsub
  have h2 : Module.finrank ℚ_[p] W ≤ Fintype.card (Fin (Module.finrank ℚ_[p] Yq) × Ms) := finrank_range_le_card fam
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at h2
  have h3 := card_xiMons (r := r) G (G.B - jp)
  calc Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ Module.finrank ℚ_[p] Yq * Ms.card := h1.trans h2
    _ ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := Nat.mul_le_mul le_rfl h3

end Level

theorem restRankL_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestRankL C0 CE1 CE2 X := by
  intro dl _ aTop _ x _
  exact finrank_Ljj_le X.p (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

section Free

variable {k σ : Type} [Field k] {r : ℕ}

theorem tieE_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) :
    Formalism.GM.tieE w e (F * m) = Formalism.GM.tieE w e F * m := by
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, mul_assoc]

theorem tieF_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tieF w e (F * m) = Formalism.GM.tieF w e F * m := by
  have key : ∀ (v : σ) (G : MvPolynomial σ k), pderiv v m = 0 → pderiv v (G * m) = pderiv v G * m := by
    intro v G hv
    rw [Derivation.leibniz, hv, smul_zero, zero_add, smul_eq_mul, mul_comm]
  unfold Formalism.GM.tieF
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  show pderiv (w c) (pderiv (e c) (F * m)) = pderiv (w c) (pderiv (e c) F) * m
  rw [key _ _ (he c), key _ _ (hw c)]

theorem tiePhi_mul_free (w e : Fin r → σ) (o n z : ℕ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tiePhi w e o n z (F * m) = Formalism.GM.tiePhi w e o n z F * m := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE w e) ^ j) (G * m) = ((Formalism.GM.tieE w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) (G * m)) =
        Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) G) * m
      rw [ih, tieE_mul_free]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF w e) ^ j) (G * m) = ((Formalism.GM.tieF w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) (G * m)) =
        Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) G) * m
      rw [ih, tieF_mul_free w e _ m hw he]
  unfold Formalism.GM.tiePhi
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, hF, hE,
    smul_mul_assoc]

theorem foldr_mul_free {ι : Type*} (l : List ι) (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (m : MvPolynomial σ k)
    (h : ∀ i ∈ l, ∀ F, f i (F * m) = f i F * m) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) (F * m) = (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F * m := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

theorem foldr_rename {τ : Type} {ι : Type*} (l : List ι) (em : σ → τ)
    (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (g : ι → MvPolynomial τ k →ₗ[k] MvPolynomial τ k)
    (h : ∀ i ∈ l, ∀ F, g i (rename em F) = rename em (f i F)) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => g i ∘ₗ acc) LinearMap.id) (rename em F) =
      rename em ((l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

end Free

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem phisB_rename_mul (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hm : ∀ (a : Fin N) (c : Fin r), pderiv (Sum.inl (Fin.castSucc a, c)) m = 0) :
    phisB p (r := r) G j jp (rename (Formalism.GM.M.chainEmb N r G.T.t) y * m) =
      rename (Formalism.GM.M.chainEmb N r G.T.t) (G.T.phis p (r := r) (G.lettersAt j jp) y) * m := by
  obtain ⟨-, hpos, -, hN⟩ := hB
  have hlt : ∀ i : Fin G.T.t, G.T.pos i + 1 < N := fun i => by have := hpos i; omega
  have hfin0 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i) =
      Fin.castSucc (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hfin1 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i + 1) =
      Fin.castSucc (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hlet0 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i) = (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hlet1 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i + 1) = (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hinj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
    intro x y h
    simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact Prod.ext h.1 h.2
  unfold phisB
  rw [foldr_mul_free]
  · congr 1
    unfold Formalism.GM.M.TieData.phis
    refine foldr_rename _ _ _ _ (fun i _ F => ?_) y
    simp only [Formalism.GM.M.TieData.phi, dif_pos (hlt i), Formalism.GM.M.tiePhiAt]
    rw [hfin0, hfin1, hlet0, hlet1]
    exact Formalism.CountingSumsFrames.TO.tiePhi_rename (Formalism.GM.M.chainEmb N r G.T.t) hinj
      (fun c : Fin r => ((⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N), c))
      (fun c : Fin r => ((⟨G.T.pos i + 1, hlt i⟩ : Fin N), c)) _ _ _ F
  · intro i _ F
    exact tiePhi_mul_free _ _ _ _ _ F m (fun c => by rw [hfin0]; exact hm _ c)
      (fun c => by rw [hfin1]; exact hm _ c)

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

theorem prod_prod_ite {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] (x : ι → α) (n : ι → ℕ) :
    ∏ a : α, ∏ i : ι, (if x i = a then n i else 0)! = ∏ i, (n i)! := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_eq_single (x i)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem smul_ite_one (n : ℕ) (c : Prop) [Decidable c] : n • (if c then 1 else 0 : ℕ) = if c then n else 0 := by
  split_ifs <;> simp

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def fL (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  (∏ i, ((if M.finPos N (G.T.pos i) = a then j i else 0)! * (if M.finPos N (G.T.pos i + 1) = a then j i else 0)!)) *
    ((if Fin.castSucc G.uPos = a then jp else 0)! * (if Fin.last N = a then jp else 0)!) *
    (∏ i, (if M.finPos N (G.T.pos i) = a then G.T.z i else 0)!) *
    (if Fin.castSucc G.uPos = a then G.zPlus else 0)! *
    (∏ a0 : Fin N, (if Fin.castSucc a0 = a then (G.lettersAt j jp).deg a0 else 0)!) *
    (if Fin.last N = a then G.B - jp else 0)!

theorem fL_dvd (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : fL G j jp a ∣ (dLvl G j jp a)! := by
  have hfac : ∀ {x y X Y : ℕ}, x ∣ X ! → y ∣ Y ! → x * y ∣ (X + Y)! := fun hx hy =>
    (mul_dvd_mul hx hy).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  unfold fL dLvl chDeg
  simp only [smul_add, smul_ite_one]
  refine hfac (hfac (hfac (hfac (hfac ?_ ?_) ?_) dvd_rfl) ?_) dvd_rfl
  · exact (Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
      Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.prod_factorial_dvd_factorial_sum _ _)
  · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
  · exact Nat.prod_factorial_dvd_factorial_sum _ _
  · exact Nat.prod_factorial_dvd_factorial_sum _ _

theorem prod_fL (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∏ a, fL G j jp a = (∏ i, (j i)!) * (∏ i, (j i)!) * (jp ! * jp !) * (∏ i, (G.T.z i)!) * G.zPlus ! *
      (∏ a0, ((G.lettersAt j jp).deg a0)!) * (G.B - jp)! := by
  have hsingle : ∀ (b : Fin (N + 1)) (n : ℕ), ∏ a, (if b = a then n else 0)! = n ! := by
    intro b n
    rw [Finset.prod_eq_single b]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  unfold fL
  simp only [Finset.prod_mul_distrib, prod_prod_ite, hsingle]

def binT (j : Fin G.T.t → ℕ) (jp : ℕ) (i : Fin G.T.t) : ℕ :=
  ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
    (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1).choose (j i)

def binP (jp : ℕ) : ℕ := ((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1).choose jp

theorem lvC_eq (j : Fin G.T.t → ℕ) (jp : ℕ) :
    lvC (r := r) G j jp * degFact G j jp = (∏ a, fL G j jp a) * ((∏ i, binT (r := r) G j jp i) * binP (r := r) G jp) := by
  rw [prod_fL]
  unfold lvC degFact binT binP
  rw [Finset.prod_mul_distrib]
  ring

theorem val_lvC_le (j : Fin G.T.t → ℕ) (jp : ℕ) (L : ℕ)
    (h1 : ∀ i, Nat.log p ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
      (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1) ≤ L)
    (h2 : Nat.log p ((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1) ≤ L) :
    padicValNat p (lvC (r := r) G j jp * degFact G j jp) ≤
      padicValNat p (∏ a, (dLvl G j jp a)!) + (G.T.t + 1) * L := by
  have hp' := hp.out
  rw [lvC_eq]
  by_cases h0 : (∏ a, fL G j jp a) * ((∏ i, binT (r := r) G j jp i) * binP (r := r) G jp) = 0
  · simp [h0, Nat.padicValNat_def]
  obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp h0
  obtain ⟨hBt, hBp⟩ := mul_ne_zero_iff.mp hB
  have hD : (∏ a, (dLvl G j jp a)!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Nat.factorial_ne_zero _
  rw [Nat.padicValNat_def, Nat.padicValNat_def,
    ← Nat.factorization_def _ hp', ← Nat.factorization_def _ hp', Nat.factorization_mul hA hB,
    Nat.factorization_mul hBt hBp]
  simp only [Finsupp.add_apply]
  have h1' : (∏ a, fL G j jp a).factorization p ≤ (∏ a, (dLvl G j jp a)!).factorization p :=
    (Nat.factorization_le_iff_dvd hA hD).mpr
      (Finset.prod_dvd_prod_of_dvd _ _ fun a _ => fL_dvd G j jp a) p
  have h2' : (∏ i, binT (r := r) G j jp i).factorization p ≤ G.T.t * L := by
    rw [Nat.factorization_prod (fun i _ => Finset.prod_ne_zero_iff.mp hBt i (Finset.mem_univ _))]
    rw [Finset.sum_apply']
    calc ∑ i, (binT (r := r) G j jp i).factorization p ≤ ∑ _i : Fin G.T.t, L :=
          Finset.sum_le_sum fun i _ => le_trans Nat.factorization_choose_le_log (h1 i)
      _ = G.T.t * L := by simp
  have h3' : (binP (r := r) G jp).factorization p ≤ L := le_trans Nat.factorization_choose_le_log h2
  rw [add_mul, one_mul]
  linarith

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
