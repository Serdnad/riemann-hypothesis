module

public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembVB
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.FrameZeroLe
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.Bundle005
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle014
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwiceValuationFactorialProduct

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G3

theorem sum_fiber_multideg {r : ℕ} (μ : ℤ × Fin r →₀ ℕ) (y : ℤ) :
    ∑ v ∈ μ.support, (if v.1 = y then μ v else 0) = multideg μ y := by
  unfold multideg
  rw [← Finset.sum_filter]
  have h1 : ∑ c : Fin r, μ (y, c) = ∑ v ∈ (Finset.univ.image fun c : Fin r => (y, c)), μ v := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (Prod.mk.inj h).2
  rw [h1]
  apply Finset.sum_subset
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_image]
    exact ⟨v.2, Finset.mem_univ _, by rw [← hv.2]⟩
  · intro v hv hnot
    rw [Finset.mem_image] at hv
    obtain ⟨c, -, rfl⟩ := hv
    by_contra h
    exact hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, rfl⟩)

theorem lkW {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) (μ : ℤ × Fin r →₀ ℕ) :
    wDeg (wSet Fr jz) μ ≤ ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) := by
  unfold wDeg
  calc ∑ v ∈ μ.support, (if v.1 ∈ wSet Fr jz then μ v else 0)
      ≤ ∑ v ∈ μ.support, ∑ m' : Fin r, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with h
        · obtain ⟨m, hm⟩ := h
          calc μ v = (if v.1 = Fr.fr (jz - 1) (r - 1 - m.val) then μ v else 0) := by rw [if_pos hm]
            _ ≤ _ := Finset.single_le_sum
              (f := fun m' : Fin r => if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
        · exact Nat.zero_le _
    _ = ∑ m' : Fin r, ∑ v ∈ μ.support, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := Finset.sum_comm
    _ = ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) :=
        Finset.sum_congr rfl fun m' _ => sum_fiber_multideg μ _

end Formalism.MainNotions.PairMembershipBlocks
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G3 Formalism.MainNotions.G.GLWeightTheory

namespace Lk

theorem homComp_eq {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf) :
    homComp d H = compD d H := rfl

theorem compD_support {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf)
    (mo : ι × Fin s →₀ ℕ) (hmo : mo ∈ (compD d H).support) : mo ∈ H.support ∧ ∀ x, multideg mo x = d x := by
  unfold compD at hmo
  obtain ⟨a, ha, hmo'⟩ := Finset.mem_biUnion.1 (support_sum hmo)
  have := support_monomial_subset hmo'
  rw [Finset.mem_singleton] at this
  subst this
  exact ⟨(Finset.mem_filter.1 ha).1, (Finset.mem_filter.1 ha).2⟩

theorem compD_sum {ι κ : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (T : Finset κ)
    (f : κ → MvPolynomial (ι × Fin s) Kf) : compD d (∑ i ∈ T, f i) = ∑ i ∈ T, compD d (f i) :=
  map_sum (AddMonoidHom.mk ⟨compD d, T5.compD_zero d⟩ (T5.compD_add d)) f T

theorem compD_eq_zero {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf)
    (h : ∀ mo ∈ H.support, ∃ x, multideg mo x ≠ d x) : compD d H = 0 := by
  unfold compD
  refine Finset.sum_eq_zero fun mo hmo => ?_
  obtain ⟨x, hx⟩ := h mo (Finset.mem_filter.1 hmo).1
  exact absurd ((Finset.mem_filter.1 hmo).2 x) hx

theorem supported_of_support {τ R : Type*} [CommSemiring R] {s : Set τ} {P Q : MvPolynomial τ R}
    (h : P.support ⊆ Q.support) (hQ : Q ∈ supported R s) : P ∈ supported R s := by
  rw [mem_supported] at hQ ⊢
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 (Finset.mem_coe.1 hv)
  exact hQ (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨d, h hd, hvd⟩))

theorem multideg_add {ι : Type} {s : ℕ} (a b : ι × Fin s →₀ ℕ) (x : ι) :
    multideg (a + b) x = multideg a x + multideg b x := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem geZ_sum {Kf : Type} [Field Kf] {ι κ : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (T : Finset κ)
    (f : κ → MvPolynomial (ι × Fin n) Kf) (t : ℝ) (h : ∀ i ∈ T, geZ (valS LL S (f i)) t) :
    geZ (valS LL S (∑ i ∈ T, f i)) t := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, valS_zero_eq_top]
    exact geZ_top _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem le_of_geZ {x : WithTop ℤ} {t : ℝ} (h : geZ x t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))

theorem geZ_coe {k : ℤ} {t : ℝ} (h : t ≤ (k : ℝ)) : geZ ((k : ℤ) : WithTop ℤ) t := by
  intro k' hk'
  have : k = k' := WithTop.coe_injective hk'
  rw [← this]
  exact h

end Lk

theorem restLink_of (hNN : ValNN) (hHD : HomDec) (hLL : LinkL) (hDg : LkDeg) (hVr : LkVars) (hTr : RestTr)
    (hW : ∀ {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) (μ : ℤ × Fin r →₀ ℕ),
      wDeg (wSet Fr jz) μ ≤ ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val))) : RestLink := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr L₁ N₁ hV hn J _ Dt hT hJ A hA l hl ga hga t ht dPl j mm hm
  obtain ⟨hEq, hcov⟩ := hTr p n' r K m O hk Fr L₁ N₁ hV hn J Dt hT A hA l hl ga hga
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set μ0 := plMon Fr p hk Dt.nL (l.mapDomain (castV hk) + ga) with hμ0
  set u := Dt.nL j + (r - 1 - mm.val) with hu
  have hur : u < Dt.nL j + r := by omega
  set Ab : ZMod J → MvPolynomial (ℤ × Fin r) (KK O) :=
    fun j' => MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')) with hAb
  set Rst : MvPolynomial (TL J Dt.nL r × Fin r) (KK O) :=
    monomial μ0 1 * ∏ j' ∈ Finset.univ.erase j, PhiJ Fr Dt j' (Ab j') with hRst
  have e1 : levP Fr p hk Dt.nL (zPl p O hk Fr A l ga) = Rst * PhiJ Fr Dt j (Ab j) := by
    rw [hEq, hRst]
    have : ∏ j' : ZMod J, Dt.ph (chi Fr Dt.nL (KK O) j' (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')))) =
        PhiJ Fr Dt j (Ab j) * ∏ j' ∈ Finset.univ.erase j, PhiJ Fr Dt j' (Ab j') :=
      (Finset.mul_prod_erase Finset.univ (fun j' => PhiJ Fr Dt j' (Ab j')) (Finset.mem_univ j)).symm
    rw [this]
    ring

  have hR0 : 0 ≤ valS Dt.trueLet (Dt.TSet j mm) Rst := by
    apply hNN
    intro v hv hvT
    rcases Finset.mem_union.1 (vars_mul _ _ hv) with h1 | h1
    · rw [vars_monomial one_ne_zero] at h1
      have h2 : μ0 v ≠ 0 := Finsupp.mem_support_iff.1 h1
      obtain ⟨⟨j'', s⟩, a⟩ := v
      cases s with
      | inl ll =>
        by_contra hs
        have hs' : Dt.sgn j'' ll = false := by
          have : Dt.trueLet.vec ⟨j'', Sum.inl ll⟩ = Dt.sgn j'' ll := rfl
          rw [this] at hs
          simpa using hs
        exact h2 (hcov j'' ll a hs')
      | inr m' => rfl
    · obtain ⟨j', hj', h2⟩ := Finset.mem_biUnion.1 (vars_prod _ h1)
      have hne : j' ≠ j := (Finset.mem_erase.1 hj').1
      rcases hVr p n' r O Fr J Dt j' (Ab j') v h2 with ⟨ll, h3⟩ | ⟨j'', m', h3⟩
      · exfalso
        rw [h3] at hvT
        rcases hvT with ⟨l', h4⟩ | ⟨m', _, h4⟩
        · exact hne (congrArg Sigma.fst h4)
        · exact hne (congrArg Sigma.fst h4)
      · rw [h3]
        rfl

  obtain ⟨Dl, hDl⟩ := hHD (KK O) ℤ r (Ab j)
  have e2 : compD dPl (Rst * PhiJ Fr Dt j (Ab j)) =
      ∑ δ ∈ Dl, compD dPl (Rst * PhiJ Fr Dt j (compD δ (Ab j))) := by
    conv_lhs => rw [hDl]

    rw [map_sum, Finset.mul_sum, Lk.compD_sum]
    rfl
  rw [e1, e2]
  refine Lk.geZ_sum _ _ _ _ _ fun δ _ => ?_
  set F := compD δ (Ab j) with hF
  have hjv : j.val < Fr.J := by
    rw [← hT.1]
    exact ZMod.val_lt j
  have hAbS : Ab j ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} := by
    have h1 := hA j.val hjv
    rw [mem_supported] at h1 ⊢
    exact fun v hv => h1 (Finset.mem_coe.2 (vars_map (A (segZ j)) (algebraMap O (KK O)) (Finset.mem_coe.1 hv)))
  have hFS : F ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} :=
    Lk.supported_of_support (fun mo hmo => (Lk.compD_support δ (Ab j) mo hmo).1) hAbS
  have hFd : ∀ μ ∈ F.support, ∀ y, multideg μ y = δ y := fun μ hμ => (Lk.compD_support δ (Ab j) μ hμ).2
  have hdeg := hDg p n' r O Fr L₁ N₁ hV J Dt hT hJ j F hFS δ hFd
  by_cases hbig : ∃ m' : Fin r, dPl ⟨j - 1, Sum.inr m'⟩ <
      multideg μ0 ⟨j - 1, Sum.inr m'⟩ + Dt.P (j - 1) m' * δ (Fr.fr (segZ j - 1) (r - 1 - m'.val))
  ·
    obtain ⟨m', hm'⟩ := hbig
    rw [Lk.compD_eq_zero, valS_zero_eq_top]
    · exact geZ_top _
    · intro mo hmo
      refine ⟨⟨j - 1, Sum.inr m'⟩, ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hmo)
      obtain ⟨a0, ha0, c, _, rfl⟩ := Finset.mem_add.1 (support_mul _ _ ha)
      have h0 := support_monomial_subset ha0
      rw [Finset.mem_singleton] at h0
      subst h0
      rw [Lk.multideg_add, Lk.multideg_add, hdeg b hb m']
      omega
  · push Not at hbig
    set dw : ℕ := ∑ m' : Fin r, δ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) with hdw
    have hwd : ∀ μ ∈ F.support, wDeg (wSet Fr (segZ j)) μ ≤ dw := by
      intro μ hμ
      refine le_trans (hW Fr (segZ j) μ) (le_of_eq ?_)
      exact Finset.sum_congr rfl fun m' _ => hFd μ hμ _
    have hdwB : (dw : ℝ) ≤ dwB Fr hk Dt dPl (l.mapDomain (castV hk) + ga) j := by
      unfold dwB
      rw [hdw]
      push_cast
      refine Finset.sum_le_sum fun m' _ => ?_
      have hP : (0 : ℝ) < (Dt.P (j - 1) m' : ℝ) := by
        have : 0 < Dt.P (j - 1) m' := pow_pos hp _
        exact_mod_cast this
      rw [le_div_iff₀ hP]
      have h1 := hbig m'
      have h2 : δ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) * Dt.P (j - 1) m' ≤
          dPl ⟨j - 1, Sum.inr m'⟩ - multideg μ0 ⟨j - 1, Sum.inr m'⟩ := by
        rw [mul_comm]
        omega
      exact_mod_cast h2
    have h1 : ((⌈t j u⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} F := by
      refine le_trans (Lk.le_of_geZ (ht j u hur)) ?_
      have h2 := (valComp (KK O) ℤ r LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} (Ab j) δ).1
      rw [Lk.homComp_eq] at h2
      refine le_trans (le_of_eq ?_) h2
      exact (Formalism.MainNotions.G.Joints.StandardMonomialSpace.valS_map (algebraMap O (KK O)) (IsFractionRing.injective O (KK O)) LZ _ _).symm
    have h3 := hLL p n' r O Fr L₁ N₁ hV hn J Dt hT hJ j mm hm F hFS dw hwd ⌈t j u⌉ h1
    have h4 : ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) ≤
        valS Dt.trueLet (Dt.TSet j mm) (compD dPl (Rst * PhiJ Fr Dt j F)) := by
      have h5 := (valComp (KK O) _ r Dt.trueLet (Dt.TSet j mm) (Rst * PhiJ Fr Dt j F) dPl).1
      rw [Lk.homComp_eq] at h5
      refine le_trans ?_ h5
      rw [mul_valS_mul]
      calc ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) = 0 + ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add hR0 h3
    refine geZ_mono h4 (Lk.geZ_coe ?_)
    have := Int.le_ceil (t j u)
    push_cast
    linarith

end Formalism.MainNotions.PairMembershipBlocks
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

namespace T5

theorem algHom_mem_supported {σ τ R : Type*} [CommSemiring R] (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (s : Set τ)
    (h : ∀ v, φ (X v) ∈ supported R s) (A : MvPolynomial σ R) : φ A ∈ supported R s := by
  induction A using MvPolynomial.induction_on with
  | C a =>
    rw [← algebraMap_eq, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ hp (h v)

theorem supp_zero {τ R : Type*} [CommSemiring R] {s : Set τ} {P : MvPolynomial τ R} (hP : P ∈ supported R s)
    {d : τ →₀ ℕ} (hd : d ∈ P.support) {v : τ} (hv : v ∉ s) : d v = 0 := by
  by_contra h
  exact hv ((mem_supported.1 hP) (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨d, hd, Finsupp.mem_support_iff.2 h⟩)))

theorem rename_mem_supported {σ τ R : Type*} [CommSemiring R] (f : σ → τ) (s : Set σ) (t : Set τ)
    (hst : ∀ v ∈ s, f v ∈ t) (A : MvPolynomial σ R) (hA : A ∈ supported R s) : rename f A ∈ supported R t := by
  rw [mem_supported] at hA ⊢
  intro w hw
  have h1 := vars_rename f A (Finset.mem_coe.1 hw)
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h1
  exact hst v (hA (Finset.mem_coe.2 hv))

end T5

section Main

variable (p : ℕ) {n' m r K : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K) (F : Frames n' r)

theorem plPart_supported (j : ℤ) (A : MvPolynomial (ℤ × Fin r) O) :
    rename (castV hk) (phSeg O K p F j (plEmb O r K A)) ∈ supported O {v : TV n' (m + 1) | v.2.val < r} := by
  have := T5.algHom_mem_supported (((rename (castV hk)).comp (phSeg O K p F j)).comp (plEmb O r K))
    {v : TV n' (m + 1) | v.2.val < r} (fun v => by
      simp only [AlgHom.comp_apply, plEmb, phSeg, rename_X, aeval_X, map_pow]
      refine Subalgebra.pow_mem _ (X_mem_supported.2 ?_) _
      show (Fin.cast hk.symm (Fin.castAdd K v.2)).val < r
      simp) A
  exact this

theorem noPart_supported (j : ℤ) (G : MvPolynomial (ℤ × Fin K) O) :
    rename (castV hk) (phSeg O K p F j (nmEmb O r K G)) ∈ supported O {v : TV n' (m + 1) | r ≤ v.2.val} := by
  have := T5.algHom_mem_supported (((rename (castV hk)).comp (phSeg O K p F j)).comp (nmEmb O r K))
    {v : TV n' (m + 1) | r ≤ v.2.val} (fun v => by
      simp only [AlgHom.comp_apply, nmEmb, phSeg, rename_X, aeval_X, map_pow]
      refine Subalgebra.pow_mem _ (X_mem_supported.2 ?_) _
      show r ≤ (Fin.cast hk.symm (Fin.natAdd r v.2)).val
      simp) G
  exact this

theorem symG_eq_mul (A : ℤ → MvPolynomial (ℤ × Fin r) O) (G : ℤ → MvPolynomial (ℤ × Fin K) O)
    (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) :
    symG p O hk F l ga (fun z => plEmb O r K (A z) * nmEmb O r K (G z)) = zPl p O hk F A l ga * zNo p O hk F G := by
  unfold symG zPl zNo
  rw [← map_mul]
  congr 1
  simp only [map_mul, Finset.prod_mul_distrib]
  ring

end Main

theorem restT_of (hGeo : RestGeo) : RestT := by
  intro p _ n' r K m _ _ _ O _ _ hk Fr L₁ N₁ hV J _ nL hJ hnL A G hA hG l hl ga hga rho dPl dNo
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hr : 1 ≤ r := NeZero.pos r
  have hGO : GeoOK Fr p nL := hGeo Fr L₁ N₁ hV p nL hJ hnL
  rw [symG_eq_mul]
  refine T5.lev_mul Fr p hk nL hp (l.mapDomain (castV hk) + ga) _ _ ?_ ?_ ?_ rho dPl dNo
  ·
    intro a ha
    have hLD : LD Fr p hk nL (rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j)))) := by
      rw [map_prod]
      refine LD_prod Fr p hk nL _ _ fun j hj => LD_phSeg Fr p hk nL hGO j (Finset.mem_range.1 hj) _ ?_
      exact T5.rename_mem_supported (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) _ _ (fun v hv => hv) _
        (hA j (Finset.mem_range.1 hj))
    have hSu : rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j))) ∈
        supported O {v : TV n' (m + 1) | v.2.val < r} := by
      rw [map_prod]
      exact Subalgebra.prod_mem _ fun j _ => plPart_supported p O hk Fr j (A j)
    have e1 : rename (castV hk) ((∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j))) * monomial l 1) *
        monomial ga 1 = rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j))) *
          monomial (l.mapDomain (castV hk) + ga) 1 := by
      rw [map_mul, MvPolynomial.rename_monomial, mul_assoc, monomial_mul, one_mul]
    have h1 := MvPolynomial.support_map_subset (algebraMap O (KK O)) _ ha
    rw [e1] at h1
    obtain ⟨d, hd, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ h1)
    have hb' := MvPolynomial.support_monomial_subset hb
    rw [Finset.mem_singleton] at hb'
    subst hb'
    refine ⟨d, hLD d hd, fun x c => T5.supp_zero hSu hd ?_, add_comm _ _⟩
    show ¬ (Fin.cast hk.symm (Fin.natAdd r c)).val < r
    simp
  ·
    intro b hb
    have hLD : LD Fr p hk nL (rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (nmEmb O r K (G j)))) := by
      rw [map_prod]
      refine LD_prod Fr p hk nL _ _ fun j hj => LD_phSeg Fr p hk nL hGO j (Finset.mem_range.1 hj) _ ?_
      exact T5.rename_mem_supported (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2))
        {v : ℤ × Fin K | v.1 ∈ Fr.letters j ∧ ¬ Fr.IsW j v.1} _ (fun v hv => hv.1) _
        (hG j (Finset.mem_range.1 hj))
    have hSu : rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (nmEmb O r K (G j))) ∈
        supported O {v : TV n' (m + 1) | r ≤ v.2.val} := by
      rw [map_prod]
      exact Subalgebra.prod_mem _ fun j _ => noPart_supported p O hk Fr j (G j)
    have h1 := MvPolynomial.support_map_subset (algebraMap O (KK O)) _ hb
    refine ⟨hLD b h1, fun x a => T5.supp_zero hSu h1 ?_⟩
    show ¬ r ≤ (Fin.cast hk.symm (Fin.castAdd K a)).val
    simp
  ·
    intro x c
    have h0 : ga (noVar Fr hk nL x c) = 0 := by
      by_contra h
      have := (hga _ h).1
      have h2 : (noVar Fr hk nL x c).2.val = r + c.val := by
        show (Fin.cast hk.symm (Fin.natAdd r c)).val = _
        simp
      omega
    have h1 : (l.mapDomain (castV hk)) (noVar Fr hk nL x c) = l (posOf n' (posTL Fr x), Fin.natAdd r c) :=
      Finsupp.mapDomain_apply_of_injective (castV_inj hk) l (posOf n' (posTL Fr x), Fin.natAdd r c)
    rw [Finsupp.add_apply, h0, add_zero, h1]
    have h3 := Formalism.MainNotions.Proposition5Numerics.tl_mem_letters hV hr hnL x
    exact hl (segZ x.1) (posTL Fr x) h3.1 h3.2 _

theorem restT : RestT := restT_of restGeo

end Formalism.MainNotions.PairMembershipBlocks
end
end
