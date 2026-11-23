module

public import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Closed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem nonneg_add_of_neg_le (c : ℝ) (x : EReal) (h : ((-c : ℝ) : EReal) ≤ x) : 0 ≤ (c : EReal) + x := by
  induction x using EReal.rec with
  | bot => simp at h
  | coe y =>
      have hy : -c ≤ y := EReal.coe_le_coe_iff.mp h
      rw [← EReal.coe_add]
      exact EReal.coe_nonneg.mpr (by linarith)
  | top => simp

theorem le_val_of_mem_span {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v)
    {s : Set R} {c : EReal} (hc : ∀ g ∈ s, c ≤ v g) : ∀ g ∈ Submodule.span (𝓞 K) s, c ≤ v g := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hc x hx
  | zero => rw [hv.zero]; exact le_top
  | add x y _ _ hx hy => exact (le_min hx hy).trans (hv.add x y)
  | smul a x _ hx =>
      rw [← algebraMap_smul K a x]
      by_cases ha : (algebraMap (𝓞 K) K a) = 0
      · rw [ha, zero_smul, hv.zero]; exact le_top
      · rw [hv.smul _ _ ha]
        have h1 : (0 : EReal) ≤ (((vAdd la (algebraMap (𝓞 K) K a) : ℤ) : ℝ) : EReal) := by
          have h0 : 0 ≤ vAdd la (algebraMap (𝓞 K) K a) := by
            unfold vAdd
            have hle : la.valuation K (algebraMap (𝓞 K) K a) ≤ 1 := la.valuation_le_one (K := K) a
            have hne : la.valuation K (algebraMap (𝓞 K) K a) ≠ 0 := by simpa using ha
            obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hne
            have hu1 : u ≤ 1 := by rw [← hu] at hle; exact_mod_cast hle
            rw [← hu, show ((u : WithZero (Multiplicative ℤ))) = WithZero.exp (Multiplicative.toAdd u) from rfl,
              WithZero.log_exp]
            have h3 : Multiplicative.toAdd u ≤ 0 := Multiplicative.toAdd_le.mpr hu1
            linarith
          exact_mod_cast h0
        calc c ≤ v x := hx
          _ = 0 + v x := (zero_add _).symm
          _ ≤ _ := add_le_add h1 le_rfl

theorem WWc_le_Mlat {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (hs : s ≠ 0) (w : WeightFamilies.Wt D j)
    (hb : ∀ G ∈ X.thAll w, ∀ la (y : X.Pt la),
      (((-(((vAdd la (s : B.KO) : ℤ) : ℝ))) : ℝ) : EReal) ≤ X.vAt la y (X.inc w G)) :
    X.WWc s w ≤ B.Mlat j w := by
  unfold WeightAlgebra.PJ.WWc
  intro F hF
  obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF
  rw [X.Mlat_eq]
  intro la y
  have hsK : ((s : B.KO)) ≠ 0 := by exact_mod_cast hs
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← algebraMap_smul B.KO s G, map_smul, X.vAt_smul la y _ _ hsK]
  exact nonneg_add_of_neg_le _ _ (hb G hG la y)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

section Letters

variable {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ)

def colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) : (Σ τ : T, Fin (rr τ)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

theorem colM_lEq_colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) :
    colM (m.mapDomain (CVA.lEq (T := T) (r := rr) (n := n))) b = colL rr n m b := by
  ext ℓ
  show Finsupp.mapDomain CVA.lEq m (CVA.lEq ⟨ℓ.1, ℓ.2, b⟩) = m ⟨ℓ.1, ℓ.2, b⟩
  rw [Finsupp.mapDomain_apply_of_injective CVA.lEq.injective]

end Letters

section Main

variable {R k : Type} [CommRing R] [Field k] [Algebra ℚ k] [Algebra R k]


theorem chartValJ (hRQ : IsRQ (R := R) k) (J : Submodule R k) (hJ1 : (1 : k) ∈ J)
    {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h)
    (w0 : O) (hw0 : w0 + star w0 = 1) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ))
    {π : Type} [Fintype π] [DecidableEq π] (c : T → π) (s : T → Bool)
    (hcs : ∀ τ, c (cc τ) = c τ ∧ s (cc τ) ≠ s τ)
    (u φ : (Σ τ : T, Fin (rr τ)) → Fin d → R) (ψ : (Σ τ : T, Fin (rr τ)) → Fin d → k) (hψ : ∀ ℓ i, ψ ℓ i ∈ J)
    (heig : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 →
      ∑ i, (algebraMap R k (φ ℓ' i) + ψ ℓ' i - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0)
    (h21a : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21b : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21c : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => (0, ψ ℓ)))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Formalism.L2.Pj.Letter T rr n) k)
    (hP : P ∈ Formalism.L2.Pj.HaO rr n k (algebraMap R k).range cc isX a)
    (e : ℕ) (he : ∀ mo ∈ P.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colL rr n mo b) ≤ e)
    (f : Fin n → PS k 1 d) (hf : ∀ b, IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ J ^ e := by
  classical
  set uK : (Σ τ : T, Fin (rr τ)) → Fin d → k := fun ℓ j => algebraMap R k (u ℓ j) with huK
  set φK : (Σ τ : T, Fin (rr τ)) → Fin d → k :=
    fun ℓ i => algebraMap R k (φ ℓ i) + ψ ℓ i - (sg1 k h).mulVec (uK ℓ) i with hφK
  set g : Fin n → PS k 1 d := fun b => FB.expS k ((m : k) • B.hL k h w0) * f b with hgdef
  set P2 := MvPolynomial.rename (CVA.lEq (T := T) (r := rr) (n := n)) P with hP2

  have hvan : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 → ∑ i, φK ℓ' i * uK ℓ i = 0 := fun ℓ ℓ' hne => heig ℓ ℓ' hne
  have hpair : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 = cc ℓ.1 → (c ℓ.1 = c ℓ'.1 ∧ s ℓ.1 ≠ s ℓ'.1) := by
    intro ℓ ℓ' he'
    rw [he']
    exact ⟨(hcs ℓ.1).1.symm, (hcs ℓ.1).2.symm⟩
  have hL1 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' _
    simp [betaH]
  have hL2 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (0, φK ℓ)) := by
    intro l l' hnot
    by_cases hl : l'.1 = cc l.1
    · exact absurd (hpair l l' hl) hnot
    · simp only [betaH, Pi.zero_apply, zero_mul, sub_zero]
      exact hvan l l' hl
  have hL3 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, φK ℓ))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' hnot
    by_cases hl : l.1 = cc l'.1
    · exfalso
      apply hnot
      have := hpair l' l hl
      exact ⟨this.1.symm, this.2.symm⟩
    · simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hl

  have hharm := CVA.harm_rename (r := rr) (n := n) cc isX P hP.1.1

  set cfun : (Σ τ : T, Fin (rr τ)) → (Σ τ : T, Fin (rr τ)) → k := fun l l' =>
    if c l.1 = c l'.1 ∧ s l.1 = true ∧ s l'.1 = false then (m : k) * betaH k (0, φK l) (uK l', 0) else 0
    with hcfun
  have hcvan : ∀ l l' : (Σ τ : T, Fin (rr τ)), l'.1 ≠ cc l.1 → cfun l l' = 0 := by
    intro l l' hne
    have hne' : l.1 ≠ cc l'.1 := fun h' => hne (by rw [h', hcc])
    have hz : betaH k (0, φK l) (uK l', 0) = 0 := by
      simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hne'
    simp only [hcfun, hz, mul_zero, ite_self]
  have hso := harmSecond_holds k T rr cc isX hcc hX n cfun hcvan P2 hharm
  have hfun : (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) =
      (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n => if p.2 = q.2 then cfun p.1 q.1 else 0) := by
    funext p q
    by_cases h1 : p.2 = q.2 <;> simp [h1, hcfun]
  have hso' : secondOrder k (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) P2 = 0 := by
    rw [hfun]
    exact hso

  have hLH := TB.WickVanishing.Closed.lemma_H_columns R d O k B h hg.ax0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1) (fun ℓ => s ℓ.1)
    uK φK hL1 hL2 hL3 n P2 hso' g

  set ξh : (Σ τ : T, Fin (rr τ)) → (Fin d → k) × (Fin d → k) := fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
      fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i) with hξh
  have hxi : (fun ℓ => ξh ℓ + ((0 : Fin d → k), ψ ℓ)) = fun ℓ => (uK ℓ, φK ℓ) := by
    funext ℓ
    refine Prod.ext ?_ ?_
    · funext j
      simp [hξh, huK]
    · funext i
      simp only [hξh, Prod.snd_add, Pi.add_apply, hφK, huK]
      ring
  have he2 : ∀ mo ∈ P2.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colM mo b) ≤ e := by
    intro mo hmo
    rw [hP2, MvPolynomial.support_rename_of_injective CVA.lEq.injective] at hmo
    obtain ⟨mo0, hmo0, rfl⟩ := Finset.mem_image.1 hmo
    simp only [colM_lEq_colL]
    exact he mo0 hmo0
  have hSC := TB.WickVanishing.Closed.scaled_connection_columns R d O k hRQ J hJ1 B h hg w0 hw0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1)
    (fun ℓ => s ℓ.1) ξh ψ (fun ℓ => ⟨u ℓ, φ ℓ, rfl⟩) hψ h21a h21b h21c n P2
    (CVA.coeff_rename_mem _ P hP.2) e he2 f hf
  rw [hxi] at hSC
  have hchain : ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) uK
      (MvPolynomial.monomial (colL rr n mo b) 1) =
      ∑ mo ∈ P2.support, P2.coeff mo * ∏ b, constantCoeff (ordNabla k B h m (fun ℓ => s ℓ.1)
        (fun ℓ => (uK ℓ, φK ℓ)) (MvPolynomial.monomial (colM mo b) 1) (liftX k (g b))) := by
    rw [hLH, hP2, CVA.sum_rename]
    refine Finset.sum_congr rfl fun mo _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [colM_lEq_colL]
    simp only [FB.nabVal, hgdef]
    rw [mul_comm]
  rw [hchain]
  have hg' : g = fun b => FB.expS k ((m : k) • B.hL k h w0) * f b := hgdef
  rw [hg']
  exact hSC

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end
