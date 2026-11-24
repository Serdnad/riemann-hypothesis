module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.InitPartZeroXMul
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FirstWeightLeOfSupport
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM

@[expose] public section

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Abs
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem proj_comm_abs' (PE A : V →ₗ[k] V) (R W L : Submodule k V) (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = R ⊓ W) (h3 : LinearMap.ker PE ⊓ W = L ⊓ W)
    (hR : ∀ x ∈ R, A x ∈ R) (hW : ∀ x ∈ W, A x ∈ W) (hL : ∀ x ∈ L, A x ∈ L) :
    ∀ x ∈ W, PE (A x) = A (PE x) := by
  intro x hx
  have hfix : ∀ y ∈ LinearMap.range PE, PE y = y := by
    rintro y ⟨z, rfl⟩
    rw [← LinearMap.comp_apply, h1]
  have hPx : PE x ∈ R ⊓ W := by
    rw [← h2]
    exact LinearMap.mem_range_self PE x
  have hA1 : A (PE x) ∈ R ⊓ W := ⟨hR _ hPx.1, hW _ hPx.2⟩
  have hA1' : PE (A (PE x)) = A (PE x) := hfix _ (by rw [h2]; exact hA1)
  have hker : x - PE x ∈ LinearMap.ker PE ⊓ W := by
    refine ⟨LinearMap.mem_ker.mpr ?_, W.sub_mem hx hPx.2⟩
    rw [map_sub, ← LinearMap.comp_apply, h1, sub_self]
  rw [h3] at hker
  have hA2 : A (x - PE x) ∈ LinearMap.ker PE ⊓ W := by
    rw [h3]
    exact ⟨hL _ hker.1, hW _ hker.2⟩
  have h0 : PE (A (x - PE x)) = 0 := hA2.1
  rw [map_sub, map_sub, hA1', sub_eq_zero] at h0
  exact h0

end Abs

section EC
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def lowIm' (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
    Submodule.map (glAct p LL j c d) ⊤

theorem lowIm_keep' (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) :
    ∀ x ∈ lowIm' p LL j ρ, A x ∈ lowIm' p LL j ρ := by
  have key : lowIm' p LL j ρ ≤ (lowIm' p LL j ρ).comap A := by
    unfold lowIm'
    refine iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_
    rintro y ⟨z, -, rfl⟩
    rw [Submodule.mem_comap, hA c hcd.1 d hcd.2.1 z]
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem hcd ⟨A z, Submodule.mem_top, rfl⟩))
  exact fun x hx => key hx

theorem hwProj_comm' (LL : Letters N) (j : ℕ) (ρ : Fin r) (la : Fin r → ℤ)
    (PE A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la)
    (h3 : LinearMap.ker PE ⊓ WtSpC p LL j univ la = lowIm' p LL j ρ ⊓ WtSpC p LL j univ la)
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x))
    (hW : ∀ x ∈ WtSpC p LL j univ la, A x ∈ WtSpC p LL j univ la) :
    ∀ x ∈ WtSpC p LL j univ la, PE (A x) = A (PE x) := by
  have hsub : WtSpC p LL j univ la ≤ WtSpC p LL j (univ.erase ρ) la := by
    intro x hx
    simp only [WtSpC, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at hx ⊢
    intro m hm c _
    exact hx (show m ∈ (↑x.support : Set _) from hm) c (Finset.mem_univ c)
  have hR : ∀ x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la,
      A x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la := by
    intro x hx
    have hAx := hW x hx.2
    refine ⟨?_, hAx⟩
    have hx1 : x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d) := hx.1
    show A x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d)
    rw [Submodule.mem_inf] at hx1 ⊢
    refine ⟨hsub hAx, ?_⟩
    have hx2 := hx1.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
    intro c d hcd
    rw [← hA c hcd.1 d hcd.2.1, hx2 c d hcd, map_zero]
  refine proj_comm_abs' PE A _ _ _ h1 ?_ h3 hR hW (lowIm_keep' LL j ρ A hA)
  rw [h2, inf_assoc, inf_idem]

theorem resL_fix' {σ : Type} (v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) : resL p v 0 x = x := by
  have hx' := hx
  simp only [FreeOf, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
    LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at hx'
  change initPart v 0 x = x
  unfold initPart
  conv_rhs => rw [x.as_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [if_pos (show m v = 0 from hx' (Finset.mem_coe.mpr hm))]

theorem fock_monomial_zero' {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (hm : m ∉ g.support) :
    fock p g (monomial m 1) = 0 := by
  classical
  unfold fock
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [MvPolynomial.coeff_monomial, if_neg (show m ≠ n from fun h => hm (by rw [h]; exact hn)), mul_zero, zero_mul]

theorem fock_right_zero' {σ : Type} (g : MvPolynomial σ ℚ_[p]) : fock p g 0 = 0 := by
  simp [fock]

theorem monomial_mem_supp' {σ : Type} (Q : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ Q) :
    monomial m (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] Q := by
  simp only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply]
  intro n hn
  rwa [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (show n ∈ (monomial m (1 : ℚ_[p])).support from hn))]

theorem cartan_comm_erase' (LL : Letters N) (j : ℕ) (ρ : Fin r) (a : Fin r) (ha : a ∈ univ.erase ρ) (b : Fin r)
    (hb : b ∈ univ.erase ρ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j ρ ρ (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j ρ ρ x) := by
  have h := glAct_comm (p := p) LL j ρ ρ a b x
  rw [if_neg (show ¬ (ρ = a) from fun h' => (Finset.mem_erase.mp ha).1 h'.symm),
    if_neg (show ¬ (b = ρ) from (Finset.mem_erase.mp hb).1), sub_zero, sub_eq_zero] at h
  exact h

end EC

theorem highest_vector_projection_of_type_projections (tight : Bool) (p : ℕ) [Fact p.Prime]
    (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ)
    (hTight : tight = true → 1 ≤ K ∧
      ∀ (j : ℕ) (T : Set (Fin r → ℤ))
        (P : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
          MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
        j ≤ 1 → 1 ≤ r → IsTypeProj p LL j univ T P →
        (∀ F ∈ Pol p r LL, P F = F) ∨ (∀ F ∈ Pol p r LL, P F = 0))
    (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hHP : HypP p LL ρ e1) (hHE : HypE p LL ρ e1) :
    ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
        MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LL m → m (Fin.last K, ρ) = 0 →
        Pr (monomial m 1) ∈ XH p LL J M ρ w ∧
        ((p : ℚ_[p]) ^ (((if tight then K else K + 2) + 1) * e1)) • Pr (monomial m 1) ∈
          IntPol p (Fin (K + 1) × Fin r) ∧
        ∀ g ∈ XH p LL J M ρ w, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1) := by
  classical
  obtain ⟨hP1, hP2⟩ := hHP
  obtain ⟨PE, hE1, hE2, hE3, hE4, hE5⟩ := hHE (K + 1) le_rfl w
  set v : Fin (K + 1) × Fin r := (Fin.last K, ρ) with hvdef
  set Wt := WtSpC p LL (K + 1) univ w with hWtdef

  let Cs : Fin (K + 2) → Finset (Fin r) := fun i => if (i : ℕ) = K + 1 then univ.erase ρ else univ
  let s : Fin (K + 2) → Finset (Fin q) := fun i =>
    univ.filter fun k => J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)
  let thr : Fin (K + 2) → WithTop ℤ := fun i => (s i).inf M
  let T : Fin (K + 2) → Set (Fin r → ℤ) := fun i => {la | ((la 0 : ℤ) : WithTop ℤ) ≤ thr i}
  have h0ρ : (0 : Fin r) ≠ ρ := by
    intro h
    have h' := congrArg Fin.val h
    have h0 : ((0 : Fin r) : ℕ) = 0 := by simp
    rw [hρ, h0] at h'
    omega
  have hCsT : ∀ i : Fin (K + 2), (i : ℕ) = K + 1 → Cs i = univ.erase ρ := fun i h => if_pos h
  have hCsL : ∀ i : Fin (K + 2), (i : ℕ) ≠ K + 1 → Cs i = univ := fun i h => if_neg h
  have hCs : ∀ i, Cs i = univ ∨ Cs i = univ.erase ρ := by
    intro i
    by_cases h : (i : ℕ) = K + 1
    · exact Or.inr (hCsT i h)
    · exact Or.inl (hCsL i h)
  have h0Cs : ∀ i, (0 : Fin r) ∈ Cs i := by
    intro i
    rcases hCs i with h | h <;> rw [h]
    · exact mem_univ _
    · exact mem_erase.mpr ⟨h0ρ, mem_univ _⟩
  have hsat : ∀ i, CsSaturated (Cs i) (T i) := fun i la la' h => by
    show ((la 0 : ℤ) : WithTop ℤ) ≤ thr i ↔ ((la' 0 : ℤ) : WithTop ℤ) ≤ thr i
    rw [h 0 (h0Cs i)]
  have hthrle : ∀ (i : Fin (K + 2)) (k : Fin q), (J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)) → thr i ≤ M k :=
    fun i k hk => Finset.inf_le (mem_filter.mpr ⟨mem_univ k, hk⟩)
  have hthrc : ∀ i : Fin (K + 2), thr i = ⊤ ∨
      ∃ k, (J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)) ∧ thr i = M k := by
    intro i
    rcases (s i).eq_empty_or_nonempty with he | hne
    · left
      show (s i).inf M = ⊤
      rw [he, Finset.inf_empty]
    · right
      obtain ⟨k, hk, hke⟩ := Finset.exists_mem_eq_inf (s i) hne M
      exact ⟨k, (mem_filter.mp hk).2, hke⟩
  have hex : ∀ i : Fin (K + 2), ∃ P, IsTypeProj p LL i (Cs i) (T i) P ∧
      (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin (K + 1) × Fin r) :=
    fun i => hP1 i (Nat.lt_succ_iff.mp i.isLt) (Cs i) (hCs i) (T i) (hsat i)
  choose P hPt hPsa hPint using hex
  have hPlow : ∀ i : Fin (K + 2), (i : ℕ) ≠ K + 1 → IsTypeProj p LL i univ (T i) (P i) := by
    intro i h
    have := hPt i
    rwa [hCsL i h] at this
  have hPtop : ∀ i : Fin (K + 2), (i : ℕ) = K + 1 → IsTypeProj p LL (K + 1) (univ.erase ρ) (T i) (P i) := by
    intro i h
    have := hPt i
    rwa [hCsT i h, h] at this
  have hPP : ∀ i x, P i (P i x) = P i x := fun i x => LinearMap.congr_fun (hPt i).1 x
  have hsub : ∀ i i' : Fin (K + 2), (i : ℕ) ≤ (i' : ℕ) → Cs i' ⊆ Cs i := by
    intro i i' h
    by_cases hi : (i : ℕ) = K + 1
    · rw [hCsT i hi, hCsT i' (by have := i'.isLt; omega)]
    · rw [hCsL i hi]; exact subset_univ _
  have hcomm : ∀ i i' x, P i (P i' x) = P i' (P i x) := by
    intro i i' x
    rcases le_total (i : ℕ) (i' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 i i' (Cs i) (Cs i') (T i) (T i') (P i) (P i') h (hsub i i' h) (hCs i)
        (hCs i') (hPt i) (hPt i')) x
    · exact (LinearMap.congr_fun (hP2 i' i (Cs i') (Cs i) (T i') (T i) (P i') (P i) h (hsub i' i h) (hCs i')
        (hCs i) (hPt i') (hPt i)) x).symm
  have hPpol : ∀ i, ∀ x ∈ Pol p r LL, P i x ∈ Pol p r LL := fun i => typeProj_polC LL i (Cs i) (T i) (P i) (hPt i)

  have hPgl : ∀ i, ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      P i (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (P i x) := by
    intro i c hc d hd x
    by_cases hi : (i : ℕ) = K + 1
    · exact typeProj_glActC LL (K + 1) _ (T i) (P i) (hPtop i hi) c hc d hd x
    · exact typeProj_comm_later LL i (K + 1) (Nat.lt_succ_iff.mp i.isLt) (T i) (P i) (hPlow i hi) c d x
  have hPcar : ∀ i c x, P i (glAct p LL (K + 1) c c x) = glAct p LL (K + 1) c c (P i x) := by
    intro i c x
    by_cases hi : (i : ℕ) = K + 1
    · by_cases hc : c = ρ
      · subst hc
        exact typeProj_commC LL (K + 1) _ (T i) (P i) (hPtop i hi) (glAct p LL (K + 1) c c)
          (fun a ha b hb x => cartan_comm_erase' LL (K + 1) c a ha b hb x) x
      · exact hPgl i c (mem_erase.mpr ⟨hc, mem_univ _⟩) c (mem_erase.mpr ⟨hc, mem_univ _⟩) x
    · exact typeProj_comm_later LL i (K + 1) (Nat.lt_succ_iff.mp i.isLt) (T i) (P i) (hPlow i hi) c c x
  have hPWt : ∀ i, ∀ x ∈ Wt, P i x ∈ Wt := fun i => comm_wtsp LL (K + 1) (P i) (hPcar i) w
  have hPres : ∀ i x, P i (resL p v 0 x) = resL p v 0 (P i x) := by
    intro i
    refine typeProj_commC LL i (Cs i) (T i) (P i) (hPt i) (resL p v 0) (fun c hc d hd x => ?_)
    refine resL_glAct LL i c d v 0 (fun i' hi' => ?_) x
    by_cases hi : (i : ℕ) = K + 1
    · rw [hCsT i hi] at hc hd
      exact ⟨fun h => Finset.ne_of_mem_erase hc (Prod.mk.inj h).2, fun h => Finset.ne_of_mem_erase hd (Prod.mk.inj h).2⟩
    · have hne : i' ≠ Fin.last K := by
        intro h
        rw [h, Fin.val_last] at hi'
        have := i.isLt
        omega
      exact ⟨fun h => hne (Prod.mk.inj h).1, fun h => hne (Prod.mk.inj h).1⟩
  have hPfree : ∀ i, ∀ x ∈ FreeOf p v, P i x ∈ FreeOf p v := by
    intro i x hx
    rw [← resL_fix' v x hx, hPres i x]
    exact resL_free v _

  have hEcomm := hwProj_comm' LL (K + 1) ρ w PE
  have hEP : ∀ i, ∀ x ∈ Wt, PE (P i x) = P i (PE x) := fun i => hEcomm (P i) hE1 hE2 hE3 (hPgl i) (hPWt i)
  have hEres : ∀ x ∈ Wt, PE (resL p v 0 x) = resL p v 0 (PE x) :=
    hEcomm (resL p v 0) hE1 hE2 hE3
      (fun c hc d hd x => resL_glAct LL (K + 1) c d v 0 (fun i' _ =>
        ⟨fun h => Finset.ne_of_mem_erase hc (Prod.mk.inj h).2, fun h => Finset.ne_of_mem_erase hd (Prod.mk.inj h).2⟩) x)
      (resL_keep_supp v 0 _)
  have hEeul : ∀ i0 : Fin (K + 1), ∀ x ∈ Wt, PE (ProjS.eulL (fun c : Fin r => (i0, c)) x) =
      ProjS.eulL (fun c : Fin r => (i0, c)) (PE x) := fun i0 =>
    hEcomm (ProjS.eulL (fun c : Fin r => (i0, c))) hE1 hE2 hE3
      (fun c _ d _ x => eul_glAct LL (K + 1) i0 c d x)
      (comm_wtsp LL (K + 1) _ (fun c x => eul_glAct LL (K + 1) i0 c c x) w)
  have hEfix : ∀ g ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ Wt, PE g = g := by
    intro g hg
    rw [← hE2] at hg
    obtain ⟨z, rfl⟩ := hg
    exact LinearMap.congr_fun hE1 z

  have hgfix : ∀ g ∈ XSp p LL J M ρ, ∀ i, P i g = g := by
    intro g hg i
    obtain ⟨hg1, hgI⟩ := Submodule.mem_inf.mp hg
    have hgP := (Submodule.mem_inf.mp hg1).1
    rw [Submodule.mem_iInf] at hgI
    by_cases hi : (i : ℕ) = K + 1
    · rcases hthrc i with ht | ⟨k, hk, ht⟩
      · refine ycondC_fix LL (K + 1) (univ.erase ρ) (mem_erase.mpr ⟨h0ρ, mem_univ _⟩) ⊤ (T i) (P i) (hPtop i hi)
          (fun la _ => ?_) g (Submodule.mem_inf.mpr ⟨?_, hgP⟩)
        · show ((la 0 : ℤ) : WithTop ℤ) ≤ thr i
          rw [ht]; exact le_top
        · refine le_ycondC LL (K + 1) (univ.erase ρ) ⊤ ⊤ (fun x _ => ?_) (fun _ _ _ _ _ _ => trivial) trivial
          rw [mem_restrictSupport_iff]
          intro m _
          exact (le_top : ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ ⊤)
      · have hk' : K + 1 ≤ J k := by omega
        have h1 := hgI k
        rw [if_pos hk'] at h1
        have h2 := (Submodule.mem_inf.mp h1).2
        have hT : T i = {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} := by
          show {la : Fin r → ℤ | ((la 0 : ℤ) : WithTop ℤ) ≤ thr i} = _
          rw [ht]
        have h3 : g ∈ LinearMap.range (P i) := by
          rw [(hPtop i hi).2.1, hT]
          exact h2
        obtain ⟨z, rfl⟩ := h3
        exact hPP i z
    · refine ycond_fix LL i (T i) (thr i) (P i) (hPlow i hi) (fun la h => h) g (Submodule.mem_inf.mpr ⟨?_, hgP⟩)
      rcases hthrc i with ht | ⟨k, hk, ht⟩
      · rw [ht]
        refine le_ycond LL i ⊤ ⊤ (fun x _ => ?_) (fun _ _ _ _ => trivial) trivial
        rw [mem_restrictSupport_iff]
        intro m _
        exact (le_top : ((wt LL i 0 m : ℤ) : WithTop ℤ) ≤ ⊤)
      · rw [ht]
        have h1 := hgI k
        have := i.isLt
        rcases hk with hk | ⟨hk1, hk2⟩
        · rw [if_neg (by omega), hk] at h1
          exact h1
        · rw [if_pos hk2] at h1
          rw [show (i : ℕ) = K by omega]
          exact (Submodule.mem_inf.mp h1).1

  let Q := lcomp P (List.finRange (K + 2))
  let f : (Fin (K + 1) × Fin r →₀ ℕ) → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] := fun m =>
    if (∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c) then PE (Q (monomial m 1)) else 0
  refine ⟨(basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f, fun m hm hmv => ?_⟩
  have hPr : (basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f (monomial m 1) = f m := by
    have := (basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr_basis ℚ_[p] f m
    rwa [coe_basisMonomials] at this
  rw [hPr]
  by_cases hw : ∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c
  · rw [show f m = PE (Q (monomial m 1)) from if_pos hw]
    set u : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] := monomial m 1 with hu
    have huP : u ∈ Pol p r LL := monomial_mem_supp' _ m hm
    have huZ : u ∈ PolZ p r LL := by
      refine Submodule.mem_inf.mpr ⟨huP, (intPol_iff_norm _).mpr fun m' => ?_⟩
      rw [hu, coeff_monomial]; split_ifs <;> simp
    have huW : u ∈ Wt := monomial_mem_supp' _ m hw
    have huF : u ∈ FreeOf p v := monomial_mem_supp' _ m hmv
    set y := Q u with hy
    have hyW : y ∈ Wt := lcomp_keep P (Wt : Set _) _ (fun j _ => hPWt j) u huW
    have hyF : y ∈ FreeOf p v := lcomp_keep P (FreeOf p v : Set _) _ (fun j _ => hPfree j) u huF
    have hyP : y ∈ Pol p r LL := lcomp_keep P (Pol p r LL : Set _) _ (fun j _ => hPpol j) u huP
    have hyfix : ∀ i, P i y = y := fun i => lcomp_fix P hPP hcomm _ i (List.mem_finRange i) _

    have hint : ((p : ℚ_[p]) ^ (e1 * (if tight then K else K + 2))) • y ∈ PolZ p r LL := by
      by_cases ht : tight
      · obtain ⟨hK, hTriv⟩ := hTight ht
        simp only [ht, if_true]
        have hl : List.finRange (K + 2) = 0 :: 1 :: ((List.finRange K).map Fin.succ).map Fin.succ := by
          rw [List.finRange_succ, List.finRange_succ]
          simp
        have hint0 := lcomp_int LL e1 P hPpol hPint (((List.finRange K).map Fin.succ).map Fin.succ) u huZ
        rw [List.length_map, List.length_map, List.length_finRange] at hint0
        have hy'P : lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u ∈ Pol p r LL :=
          lcomp_keep P (Pol p r LL : Set _) _ (fun j _ => hPpol j) u huP
        have hyy : y = lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u ∨ y = 0 := by
          have hy2 : y = P 0 (P 1 (lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u)) := by
            rw [hy]
            show lcomp P (List.finRange (K + 2)) u = _
            rw [hl, lcomp_cons, lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply]
          rw [hy2]
          rcases hTriv _ (T 1) (P 1) (by simp) (by omega) (hPlow 1 (by simp; omega)) with h1 | h1
          · rw [h1 _ hy'P]
            rcases hTriv _ (T 0) (P 0) (by simp) (by omega) (hPlow 0 (by simp)) with h0 | h0
            · exact Or.inl (h0 _ hy'P)
            · exact Or.inr (h0 _ hy'P)
          · rw [h1 _ hy'P, map_zero]
            exact Or.inr rfl
        rcases hyy with h | h
        · rw [h]
          exact hint0
        · rw [h, smul_zero]
          exact Submodule.zero_mem _
      · simp only [ht, if_false]
        simpa [List.length_finRange] using
          lcomp_int LL e1 P hPpol hPint (List.finRange (K + 2)) u huZ
    set z := PE y with hz
    have hzfix : ∀ i, P i z = z := fun i => by rw [hz, ← hEP i y hyW, hyfix i]
    have hzR : z ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ Wt := hE2 ▸ LinearMap.mem_range_self PE y
    have hzP : z ∈ Pol p r LL := by
      rw [pol_iff_eul] at hyP ⊢
      intro i
      rw [hz, ← hEeul i y hyW, hyP i, map_smul]
    have hzF : z ∈ FreeOf p v := by
      have h1 : resL p v 0 z = z := by rw [hz, ← hEres y hyW, resL_fix' v y hyF]
      rw [← h1]
      exact resL_free v z
    have hzX : z ∈ XSp p LL J M ρ := by
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hzP, hzF⟩, (Submodule.mem_iInf _).mpr fun k => ?_⟩
      split_ifs with hk
      · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 := typeProj_range_le_ycond LL K (T ⟨K, by omega⟩) (M k) (P ⟨K, by omega⟩)
            (hPlow ⟨K, by omega⟩ (by simp))
            (fun la hla => le_trans hla (hthrle ⟨K, by omega⟩ k (Or.inr ⟨le_rfl, hk⟩))) z
          rwa [hzfix] at h1
        · have h1 : z ∈ LinearMap.range (P ⟨K + 1, by omega⟩) := ⟨z, hzfix _⟩
          rw [(hPtop ⟨K + 1, by omega⟩ rfl).2.1] at h1
          exact (iSup₂_le fun la hla => le_iSup₂_of_le (f := fun (la : Fin r → ℤ)
            (_ : ((la 0 : ℤ) : WithTop ℤ) ≤ M k) => IsoC p LL (K + 1) (univ.erase ρ) la) la
            (le_trans hla (hthrle ⟨K + 1, by omega⟩ k (Or.inr ⟨Nat.le_succ K, hk⟩))) le_rfl) h1
      · have h1 := typeProj_range_le_ycond LL (J k) (T ⟨J k, by omega⟩) (M k) (P ⟨J k, by omega⟩)
          (hPlow ⟨J k, by omega⟩ (by simp; omega))
          (fun la hla => le_trans hla (hthrle ⟨J k, by omega⟩ k (Or.inl rfl))) z
        rwa [hzfix] at h1
    refine ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hzX, (Submodule.mem_inf.mp hzR).1⟩,
      (Submodule.mem_inf.mp hzR).2⟩, ?_, ?_⟩
    · have h5 := hE5 _ hint (Wt.smul_mem _ hyW)
      rw [map_smul, smul_smul, ← pow_add] at h5
      rw [show ((if tight then K else K + 2) + 1) * e1 =
          e1 + e1 * (if tight then K else K + 2) by ring]
      exact h5
    · intro g hg
      obtain ⟨hg1, hgW⟩ := Submodule.mem_inf.mp hg
      obtain ⟨hgX, hgH⟩ := Submodule.mem_inf.mp hg1
      rw [hz, ← hE4 g y hgW hyW, hEfix g (Submodule.mem_inf.mpr ⟨hgH, hgW⟩)]
      exact lcomp_fock P hPsa g (hgfix g hgX) _ u
  · rw [show f m = 0 from if_neg hw]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, fun g hg => ?_⟩
    rw [fock_right_zero', fock_monomial_zero']
    intro hmg
    have hgW := (Submodule.mem_inf.mp hg).2
    rw [WtSpC, mem_restrictSupport_iff] at hgW
    exact hw (hgW (Finset.mem_coe.mpr hmg))

theorem highest_vector_projection : ProjX := by
  intro p _ K r _ LL q J M ρ w e1 hr hρ hv hP hE
  exact highest_vector_projection_of_type_projections false p K r LL J M ρ w e1
    (fun h => Bool.noConfusion h) hr hρ hv hP hE

end Formalism.InvariantFactorPaths.L4
