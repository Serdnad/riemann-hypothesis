module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem expS_zero' {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem cc_expS {n : ℕ} (F : PS k n d) (hF : constantCoeff F = 0) : constantCoeff (FB.expS k F) = 1 := by
  have ha : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have h1 : PowerSeries.exp k = 1 + (PowerSeries.exp k - 1) := by ring
  have h2 : PowerSeries.constantCoeff (PowerSeries.exp k - 1) = 0 := by simp
  unfold FB.expS
  rw [h1, ← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, map_add (f := _), PowerSeries.coe_substAlgHom ha,
    PowerSeries.constantCoeff_subst_eq_zero hF _ h2, map_one, add_zero]

def embX (d : ℕ) : Fin 1 × Fin d ↪ Fin d ⊕ Fin d :=
  ⟨fun p => Sum.inl p.2, fun p q hpq => by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only [Sum.inl.injEq] at hpq
    rw [Subsingleton.elim a b, hpq]⟩

theorem liftX_eq_rename (f : PS k 1 d) : liftX k f = rename (embX d) f := by
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem cc_liftX (f : PS k 1 d) : constantCoeff (liftX k f) = constantCoeff f := by
  rw [liftX_eq_rename, MvPowerSeries.constantCoeff_rename]

theorem intAA_liftX (f : PS k 1 d) (hf : IntAA (R := R) k f) : IntAA (R := R) k (liftX k f) := by
  rw [liftX_eq_rename]
  intro n
  rw [MvPowerSeries.coeff_rename]
  exact Subring.sum_mem _ fun u _ => hf u

def GoodE (R : Type) [CommRing R] [Algebra R k] (E0 X : AA k d) : Prop :=
  ∃ G : AA k d, IntAA (R := R) k G ∧ X = E0 * G

theorem good_pow (E0 : AA k d) (T : Module.End k (AA k d)) (hT : ∀ X, GoodE R E0 X → GoodE R E0 (T X))
    (n : ℕ) : ∀ X, GoodE R E0 X → GoodE R E0 ((T ^ n) X) := by
  induction n with
  | zero =>
    intro X hX
    rw [pow_zero]
    exact hX
  | succ n ih =>
    intro X hX
    rw [pow_succ]
    exact ih (T X) (hT X hX)

theorem good_prod (E0 : AA k d) (L : List (Module.End k (AA k d)))
    (hL : ∀ T ∈ L, ∀ X, GoodE R E0 X → GoodE R E0 (T X)) : ∀ X, GoodE R E0 X → GoodE R E0 (L.prod X) := by
  induction L with
  | nil =>
    intro X hX
    rw [List.prod_nil]
    exact hX
  | cons T L ih =>
    intro X hX
    rw [List.prod_cons]
    exact hL T (by simp) _ (ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) X hX)

theorem good_ofFn (E0 : AA k d) {r : ℕ} (a : Fin r → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (e : Fin r → ℕ) :
    ∀ X, GoodE R E0 X → GoodE R E0 ((List.ofFn fun i => a i ^ e i).prod X) := by
  refine good_prod E0 _ ?_
  intro T hT
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact good_pow E0 (a i) (ha i) (e i)

theorem cc_ordEval_mem (J : Submodule R k) (e : ℕ) (E0 : AA k d) (hE0 : constantCoeff E0 = 1) {r q : ℕ}
    (a : Fin r → Module.End k (AA k d)) (a' : Fin q → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (ha' : ∀ j X, GoodE R E0 X → GoodE R E0 (a' j X))
    (σ : AA k d) (hσ : GoodE R E0 σ) (Q : MvPolynomial (Fin r ⊕ Fin q) k) (hQ : ∀ mo, Q.coeff mo ∈ J ^ e) :
    constantCoeff (PI.WickFormula.ordEval a a' Q σ) ∈ J ^ e := by
  unfold PI.WickFormula.ordEval

  rw [LinearMap.sum_apply, map_sum]
  refine Submodule.sum_mem _ fun mo _ => ?_
  have hgood : GoodE R E0 (((List.ofFn fun i => a i ^ mo (Sum.inl i)).prod *
      (List.ofFn fun j => a' j ^ mo (Sum.inr j)).prod) σ) :=
    good_ofFn E0 a ha _ _ (good_ofFn E0 a' ha' _ σ hσ)
  obtain ⟨G, hGi, hGe⟩ := hgood
  rw [LinearMap.smul_apply, hGe, MvPowerSeries.smul_eq_C_mul, map_mul, map_mul,
    MvPowerSeries.constantCoeff_C, hE0, one_mul]
  obtain ⟨r, hr⟩ := hGi 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← hr, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hQ mo)

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

def ExpAddZeroConstant : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d : ℕ) (f g : PS k n d), constantCoeff f = 0 →
    constantCoeff g = 0 → FB.expS k (f + g) = FB.expS k f * FB.expS k g

def ConstantCoeffSubstitution : Prop :=
  ∀ (k : Type) [CommRing k] (d m n : ℕ) (a : Fin m → Pt k n d) (f : PS k m d),
    (∀ j i, constantCoeff (a j i) = 0) → constantCoeff (ev a f) = constantCoeff f

def IsBiadd {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (g : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] g = 0 ∧ ev (n := 1) ![pt k d 0, 0] g = 0 ∧
    ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] g ∧
    ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] g ∧
    ∀ a : O, ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] g =
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] g

def CanonicalGaugeDiffBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d),
    B.IsCanonGauge k h → B.IsCanonGauge k h' → IsBiadd B k (h' - h)

def QuadraticFormDerivatives : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (g : PS k 2 d), IsBiadd B k g → ∀ w0 : O,
    constantCoeff (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g) = 0 ∧
    (∀ u, constantCoeff (Dof (B.FK k) u (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g)) = 0) ∧
    ∀ u v, Dof (B.FK k) u (Dof (B.FK k) v (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g)) =
      C (dotProduct u ((bilinPart k g).mulVec ((dAct k B w0).mulVec v)) +
        dotProduct v ((bilinPart k g).mulVec ((dAct k B w0).mulVec u)))

def WickOperatorVanishing : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (c : ι → ι → k) (P : MvPolynomial ι k) (q : PS k 1 d),
    (∀ l l', c l l' = c l' l) → constantCoeff q = 0 → (∀ l, constantCoeff (Dof F (u l) q) = 0) →
    (∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) → secondOrder k c P = 0 →
    ∀ (m : k) (G : PS k 1 d),
      constantCoeff (DpolyOf F u P (G * FB.expS k (m • q))) = constantCoeff (DpolyOf F u P G)

end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Mon
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

end Mon

section abelian₂
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)

def lamW (P : MvPolynomial ι k) : k :=
  (AddMonoidAlgebra.coeff P).sum (fun n a => a * ψ (word (Finset.univ : Finset ι).toList n))

theorem lamW_add (P Q : MvPolynomial ι k) : lamW ψ (P + Q) = lamW ψ P + lamW ψ Q := by
  show (AddMonoidAlgebra.coeff P + AddMonoidAlgebra.coeff Q).sum _ = _
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem lamW_monomial (n : ι →₀ ℕ) (a : k) :
    lamW ψ (MvPolynomial.monomial n a) = a * ψ (word (Finset.univ : Finset ι).toList n) := by
  show (Finsupp.single n a).sum _ = _
  exact Finsupp.sum_single_index (zero_mul _)

theorem lamW_sum (s : Finset ι) (f : ι → MvPolynomial ι k) :
    lamW ψ (∑ i ∈ s, f i) = ∑ i ∈ s, lamW ψ (f i) := by
  let L : MvPolynomial ι k →+ k :=
    { toFun := lamW ψ, map_zero' := by simpa using lamW_add ψ 0 0, map_add' := lamW_add ψ }
  exact map_sum L f s

def rW (c : ι → ι → k) (n : ι →₀ ℕ) : k :=
  ((Finset.univ : Finset ι).toList.map (fun x => ((Finset.univ : Finset ι).toList.map (fun y =>
    c x y * ((n y * (n - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
      ψ (word (Finset.univ : Finset ι).toList (n - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum

theorem secondOrder_add (c : ι → ι → k) (p q : MvPolynomial ι k) :
    secondOrder k c (p + q) = secondOrder k c p + secondOrder k c q := by
  unfold secondOrder
  simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]
  done

theorem lamW_secondOrder (c : ι → ι → k) (P : MvPolynomial ι k) :
    lamW ψ (secondOrder k c P) = (AddMonoidAlgebra.coeff P).sum (fun n a => a * rW ψ c n) := by
  refine MvPolynomial.induction_on' P (fun n a => ?_) (fun p q hp hq => ?_)
  · show lamW ψ (secondOrder k c (MvPolynomial.monomial n a)) =
      (Finsupp.single n a).sum fun m b => b * rW ψ c m
    have hL : ∀ g : ι → k, ((Finset.univ : Finset ι).toList.map g).sum = ∑ i, g i := by
      intro g
      first
        | exact Finset.sum_map_toList _ _
        | exact Finset.sum_toList _ _
        | rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
    rw [Finsupp.sum_single_index (zero_mul _)]
    simp only [secondOrder, lamW_sum, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial,
      lamW_monomial, rW, hL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Nat.cast_mul]
    ring
  · rw [secondOrder_add, lamW_add, hp, hq]
    show _ = (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q).sum _
    rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

end abelian₂

end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology

variable {g : ℕ}

theorem mD_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) :
    mD f 0 s = mD h 0 s := by
  unfold mD lD
  rw [((hfh.iteratedFDeriv ℂ _).eq_of_nhds)]

theorem tay_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) : tay f s = tay h s := by
  ext n
  show mD f 0 (dirs n + s) / fct n = mD h 0 (dirs n + s) / fct n
  rw [mD_local hfh]

theorem mD_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : mD (f + h) 0 s = mD f 0 s + mD h 0 s := by
  unfold mD lD
  rw [iteratedFDeriv_add_apply (hf.of_le le_top) (hh.of_le le_top)]
  rfl

theorem tay_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : tay (f + h) s = tay f s + tay h s := by
  ext n
  rw [map_add (f := _)]
  show mD (f + h) 0 (dirs n + s) / fct n = mD f 0 (dirs n + s) / fct n + mD h 0 (dirs n + s) / fct n
  rw [mD_add hf hh, add_div]

theorem mD_zero (θ : (Fin g → ℂ) → ℂ) : mD θ 0 0 = θ 0 := by
  have key : ∀ l : List (Fin g → ℂ), l = [] →
      iteratedFDeriv ℂ l.length θ 0 (fun i => l.get i) = θ 0 := by
    rintro l rfl
    simp
  exact key _ (Multiset.toList_eq_nil.2 rfl)

theorem mD_const (c : ℂ) (s : Multiset (Fin g → ℂ)) :
    mD (fun _ : Fin g → ℂ => c) 0 s = if s = 0 then c else 0 := by
  by_cases hs : s = 0
  · subst hs
    have key : ∀ l : List (Fin g → ℂ), l = [] →
        iteratedFDeriv ℂ l.length (fun _ : Fin g → ℂ => c) 0 (fun i => l.get i) = c := by
      rintro l rfl
      simp
    rw [if_pos rfl]
    exact key _ (Multiset.toList_eq_nil.2 rfl)
  · have hlen : s.toList.length ≠ 0 := by
      rw [Multiset.length_toList]
      exact fun h0 => hs (Multiset.card_eq_zero.1 h0)
    unfold mD lD
    rw [iteratedFDeriv_const_of_ne hlen, if_neg hs]
    rfl

theorem tay_const (c : ℂ) : tay (g := g) (fun _ => c) 0 = C c := by
  ext n
  rw [MvPowerSeries.coeff_C]
  show mD (fun _ => c) 0 (dirs n + 0) / fct n = _
  rw [add_zero, mD_const]
  by_cases hn : n = 0
  · subst hn
    simp [dirs, fct]
  · have hd : dirs n ≠ 0 := by
      intro h0
      apply hn
      have h1 : Finsupp.toMultiset n = 0 := by simpa [dirs] using h0
      simpa using congrArg Multiset.toFinsupp h1
    rw [if_neg hd, if_neg hn, zero_div]

theorem mD_cons_deriv {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (t : Multiset (Fin g → ℂ)) :
    mD θ 0 (v ::ₘ t) = mD (fun y => fderiv ℂ θ y v) 0 t := by
  have ht : ((t.toList : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) = t := Multiset.coe_toList t
  have hperm : (v ::ₘ t) = ((t.toList ++ [v] : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) := by
    conv_lhs => rw [← ht]
    rw [Multiset.cons_coe, Multiset.coe_eq_coe]
    exact (List.perm_append_singleton v t.toList).symm
  have hlen : (t.toList ++ [v]).length = t.toList.length + 1 := by simp
  rw [hperm, mD_coe hθ, lD_eq θ 0 (t.toList ++ [v]) hlen, iteratedFDeriv_succ_apply_right]
  have hf : ContDiffAt ℂ ω (fderiv ℂ θ) 0 := hθ.fderiv_right (by simp)
  have hcomp : (fun y => fderiv ℂ θ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ (fderiv ℂ θ) := rfl
  unfold mD lD
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf le_top]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  congr 1
  · congr 1
    funext i
    simp only [Fin.init]
    exact List.getElem_append_left i.isLt
  · simp

theorem deriv_analytic {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) :
    ContDiffAt ℂ ω (fun y => fderiv ℂ θ y v) 0 :=
  (hθ.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem pderiv_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (j : Fin g) :
    MvPowerSeries.pderiv ((0 : Fin 1), j) (tay θ 0) =
      tay (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 := by
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  show mD θ 0 (dirs (n + Finsupp.single ((0 : Fin 1), j) 1) + 0) / fct (n + Finsupp.single ((0 : Fin 1), j) 1) * ((n ((0 : Fin 1), j) : ℂ) + 1) =
    mD (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 (dirs n + 0) / fct n
  have hd : dirs (n + Finsupp.single ((0 : Fin 1), j) 1) = (Pi.single j 1 : Fin g → ℂ) ::ₘ dirs n := by
    unfold dirs
    rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add (f := _),
      Multiset.map_singleton, add_comm, Multiset.singleton_add]
  have hf : fct (n + Finsupp.single ((0 : Fin 1), j) 1) = fct n * ((n ((0 : Fin 1), j) : ℂ) + 1) := by
    unfold fct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((0 : Fin 1), j)),
      ← Finset.mul_prod_erase Finset.univ (fun p => ((n p).factorial : ℂ)) (Finset.mem_univ ((0 : Fin 1), j))]
    have hrest : ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), (((n + Finsupp.single ((0 : Fin 1), j) 1 : Fin 1 × Fin g →₀ ℕ) x).factorial : ℂ) =
        ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), ((n x).factorial : ℂ) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
    rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
    push_cast
    ring
  have hne : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [add_zero, add_zero, hd, mD_cons_deriv hθ, hf, ← div_div, div_mul_cancel₀ _ hne]

theorem deriv_mul_ev {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) (v : Fin g → ℂ) :
    (fun y => fderiv ℂ (f * h) y v) =ᶠ[𝓝 0]
      (fun y => fderiv ℂ f y v) * h + f * (fun y => fderiv ℂ h y v) := by
  filter_upwards [hf.eventually (by simp), hh.eventually (by simp)] with y hy1 hy2
  rw [fderiv_mul (hy1.differentiableAt (by simp)) (hy2.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.mul_apply]
  ring

theorem taylor_mul_coeff_low_degree (N : ℕ) : ∀ (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    ∀ n : Fin 1 × Fin g →₀ ℕ, n.degree < N → coeff n (tay (f * h) 0) = coeff n (tay f 0 * tay h 0) := by
  induction N with
  | zero =>
    intro f h _ _ n hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ N ih =>
    intro f h hf hh n hn
    by_cases h0 : n = 0
    · subst h0
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
      simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show mD (f * h) 0 (dirs 0 + 0) / fct 0 = (mD f 0 (dirs 0 + 0) / fct 0) * (mD h 0 (dirs 0 + 0) / fct 0)
      simp [dirs, fct, mD_zero]
    · obtain ⟨x, hx⟩ : ∃ x, n x ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Finsupp.ext hc)
      obtain ⟨i, j⟩ := x
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      obtain ⟨m, hm⟩ : ∃ m, m = n - Finsupp.single ((0 : Fin 1), j) 1 := ⟨_, rfl⟩
      have hnm : n = m + Finsupp.single ((0 : Fin 1), j) 1 := by
        rw [hm]
        exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hx))).symm
      have hmdeg : m.degree < N := by
        have h1 : n.degree = m.degree + 1 := by
          rw [hnm, map_add (f := _), Finsupp.degree_single]
        omega
      have key : ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ,
          coeff m (MvPowerSeries.pderiv ((0 : Fin 1), j) F) =
            coeff n F * ((m ((0 : Fin 1), j) : ℂ) + 1) := fun F => by
        rw [MvPowerSeries.coeff_pderiv, ← hnm]
      have hc : ((m ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
      apply mul_right_cancel₀ hc
      rw [← key, ← key]
      have hfh : ContDiffAt ℂ ω (f * h) 0 := hf.mul hh
      have hf' := deriv_analytic hf (Pi.single j 1)
      have hh' := deriv_analytic hh (Pi.single j 1)
      rw [pderiv_tay hfh, tay_local (deriv_mul_ev hf hh (Pi.single j 1)), tay_add (f := (fun y => fderiv ℂ f y (Pi.single j 1)) * h)
        (h := f * fun y => fderiv ℂ h y (Pi.single j 1)) (hf'.mul hh) (hf.mul hh'),
        map_add, Derivation.leibniz, pderiv_tay hf, pderiv_tay hh, ih _ _ hf' hh m hmdeg,
        ih _ _ hf hh' m hmdeg, smul_eq_mul, smul_eq_mul, map_add, mul_comm (tay h 0)]
      ring

theorem taylor_multiplication : TaylorMulSt := by
  refine ⟨fun g f h hf hh => ⟨?_, tay_add hf hh 0⟩, fun g c => tay_const c,
    fun g f h hfh => tay_local hfh 0⟩
  ext n
  exact taylor_mul_coeff_low_degree (n.degree + 1) f h hf hh n (Nat.lt_succ_self _)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
end
end
