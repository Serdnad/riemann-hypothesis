module

public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

@[expose] public section

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RgDsTor

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW PositivityTheory.RgDs.K

variable {n : ℕ}

theorem diagI_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  unfold inK inG Jm
  refine ⟨?_, ?_⟩
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext a
    simp [star_mul]
    split_ifs <;> ring
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem tor_eq_exp (θ : Fin n → ℝ) :
    tor θ = NormedSpace.exp (((1 : ℝ) : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  rw [Complex.ofReal_one, one_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [Complex.exp_eq_exp_ℂ]

private theorem pow_apply_eq_pow_smul_of_apply_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) (k : ℕ) : (A ^ k) w = c ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']

theorem exp_apply_of_eigen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) :
    NormedSpace.exp A w = Complex.exp c • w := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V w)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const w
  rw [← Complex.exp_eq_exp_ℂ] at h2
  have h3 : HasSum (fun k : ℕ => (ContinuousLinearMap.apply ℂ V w) (((k.factorial : ℂ))⁻¹ • A ^ k))
      (Complex.exp c • w) := by
    convert h2 using 1
    funext k
    rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      pow_apply_eq_pow_smul_of_apply_eq_smul A c w h k, smul_smul, smul_eq_mul]
  have e := h1.unique h3
  rwa [ContinuousLinearMap.apply_apply] at e

private theorem diagonal_mul_I_eq_sum_single (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      ∑ a, ((θ a : ℂ) * Complex.I) • Matrix.single a a (1 : ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

theorem dtau_diag_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (θ : Fin n → ℝ) :
    T.dτ (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) T.w =
      (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • T.w := by

  rw [diagonal_mul_I_eq_sum_single, map_sum, ContinuousLinearMap.sum_apply]
  simp_rw [map_smul, ContinuousLinearMap.smul_apply, T.13, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem torW : TorW := by
  intro n ε Λ T θ k hk
  have hX := diagI_inK ε θ
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ 1, hk, tor_eq_exp])
  rw [← h1, KType.op_curve T hX γ hγ 1]
  apply exp_apply_of_eigen
  rw [ContinuousLinearMap.smul_apply, dtau_diag_w, smul_smul, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.RgDsTor
end
end

section

noncomputable section

open Finset MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.WordFam

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem eword_smooth (hP : IsPsiFor ε lam T Ψ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), IsSmoothL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v))
  | [] => datumFunction_isSmoothL2 hP T.w v
  | p :: w => (eword_smooth hP v w).Eab p.1 p.2

def cD (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : smD ε (rreg ε) :=
  ⟨toL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v)), toL2_mem_smD_of_isSmoothL2 (eword_smooth hP v w)⟩

theorem cD_cons (hP : IsPsiFor ε lam T Ψ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (v : T.V) :
    cD hP (p :: w) v = smE ε (rreg ε) p.1 p.2 (cD hP w v) :=
  Subtype.ext (rightDerivative_toL2 (eword_smooth hP v w) p.1 p.2).symm

theorem cD_add (hP : IsPsiFor ε lam T Ψ) (u v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (u + v) = cD hP w u + cD hP w v
  | [] => Subtype.ext (datumEmbedding_add hP T.w u v)
  | p :: w => by rw [cD_cons, cD_cons, cD_cons, cD_add hP u v w, map_add (f := _)]

theorem cD_smul (hP : IsPsiFor ε lam T Ψ) (c : ℂ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (c • v) = c • cD hP w v
  | [] => Subtype.ext (datumEmbedding_smul hP T.w c v)
  | p :: w => by rw [cD_cons, cD_cons, cD_smul hP c v w, map_smul]

theorem cD_zero (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) : cD hP w (0 : T.V) = 0 := by
  simpa using cD_smul hP (0 : ℂ) (0 : T.V) w

theorem actL_eq (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) :
    actL T Ψ a = ∑ x, (cD hP (ofW x) (a x) : L2 ε) := by
  have h := toL2_finset_sum_of_memLp (ε := ε) univ
    (fun x : Wd n m => Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)))
    (fun x => (eword_smooth hP (a x) (ofW x)).2 [])
  have e : actF T Ψ a = fun g => ∑ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)) g := by
    funext g
    exact Finset.sum_apply _ _ _
  unfold actL
  rw [e]
  exact h

theorem ofW_inj {m : ℕ} {x y : Wd n m} (h : ofW x = ofW y) : x = y := by
  obtain ⟨⟨l, hl⟩, w⟩ := x
  obtain ⟨⟨l', hl'⟩, w'⟩ := y
  have hlen : l = l' := by simpa [ofW] using congrArg List.length h
  subst hlen
  have : w = w' := List.ofFn_injective h
  subst this
  rfl


open Classical in
def sgl (m : ℕ) (w : List (Fin n × Fin n)) (v : T.V) : AS T m := fun y => if ofW y = w then v else 0

theorem actL_sgl (hP : IsPsiFor ε lam T Ψ) {m : ℕ} {w : List (Fin n × Fin n)} (h : w.length ≤ m) (v : T.V) :
    actL T Ψ (sgl m w v) = (cD hP w v : L2 ε) := by
  have hx0 : ofW (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m) = w := List.ofFn_get w
  rw [actL_eq hP, Finset.sum_eq_single (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m)]
  · simp only [sgl, hx0, if_true]
  · intro y _ hy
    have hne : ofW y ≠ w := fun e => hy (ofW_inj (e.trans hx0.symm))
    simp only [sgl, if_neg hne, cD_zero]
    rfl
  · intro hn
    exact absurd (Finset.mem_univ _) hn

def actLin (hP : IsPsiFor ε lam T Ψ) (m : ℕ) : AS T m →ₗ[ℂ] L2 ε where
  toFun := actL T Ψ
  map_add' a b := by
    simp only [actL_eq hP, Pi.add_apply, cD_add, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [actL_eq hP, Pi.smul_apply, cD_smul, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply]

theorem actLin_apply (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) : actLin hP m a = actL T Ψ a := rfl

theorem pad (hP : IsPsiFor ε lam T Ψ) {m m' : ℕ} (h : m ≤ m') (a : AS T m) :
    ∃ a' : AS T m', actL T Ψ a' = actL T Ψ a := by
  refine ⟨∑ x : Wd n m, sgl m' (ofW x) (a x), ?_⟩

  rw [← actLin_apply hP, map_sum, actL_eq hP a]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [actLin_apply, actL_sgl hP]
  have : (ofW x).length = x.1 := by simp [ofW]
  have h2 := x.1.2
  omega

def exS (hP : IsPsiFor ε lam T Ψ) : Submodule ℂ (smD ε (rreg ε)) where
  carrier := {x | ∃ (m : ℕ) (a : AS T m), (x : L2 ε) = actL T Ψ a}
  add_mem' := by
    rintro x y ⟨m, a, ha⟩ ⟨m', b, hb⟩
    obtain ⟨a', ea⟩ := pad hP (le_max_left m m') a
    obtain ⟨b', eb⟩ := pad hP (le_max_right m m') b
    refine ⟨_, a' + b', ?_⟩
    rw [Submodule.coe_add, ha, hb, ← ea, ← eb]
    exact ((actLin hP _).map_add a' b').symm
  zero_mem' := ⟨0, 0, ((actLin hP 0).map_zero).symm⟩
  smul_mem' := by
    rintro c x ⟨m, a, ha⟩
    refine ⟨m, c • a, ?_⟩
    rw [Submodule.coe_smul, ha]
    exact ((actLin hP m).map_smul c a).symm

theorem cD_mem_exS (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : cD hP w v ∈ exS hP :=
  ⟨w.length, sgl _ w v, (actL_sgl hP le_rfl v).symm⟩

theorem eq_sum (hP : IsPsiFor ε lam T Ψ) {x : smD ε (rreg ε)} {m : ℕ} {a : AS T m}
    (h : (x : L2 ε) = actL T Ψ a) : x = ∑ y, cD hP (ofW y) (a y) :=
  Subtype.ext (by rw [h, actL_eq hP, Submodule.coe_sum])

theorem genSub_le_exS (hP : IsPsiFor ε lam T Ψ) :
    genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) ≤ exS hP := by
  refine sInf_le ⟨fun x hx => ?_, fun a b x hx => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 hx
    have : x = cD hP [] v := Subtype.ext hv
    rw [this]
    exact cD_mem_exS hP [] v
  · obtain ⟨m, f, hf⟩ := hx

    rw [eq_sum hP hf, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    have := cD_cons hP (a, b) (ofW y) (f y)
    simp only at this
    rw [← this]
    exact cD_mem_exS hP _ _

theorem cD_mem_genSub (hP : IsPsiFor ε lam T Ψ) (v : T.V) (w : List (Fin n × Fin n)) :
    cD hP w v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) := by
  refine (Submodule.mem_sInf).2 fun N hN => ?_
  induction w with
  | nil => exact hN.1 ((mem_datumV_iff hP T.w _).2 ⟨v, rfl⟩)
  | cons p w ih =>
    rw [cD_cons]
    exact hN.2 _ _ _ ih

theorem exhaust : Exhaust := by
  intro n ε lam T Ψ hP
  refine ⟨fun x hx => genSub_le_exS hP hx, fun m m' h a => pad hP h a, fun m a => ?_⟩
  refine ⟨∑ x, cD hP (ofW x) (a x),
    Submodule.sum_mem _ fun x _ => cD_mem_genSub hP _ _, ?_⟩
  rw [actL_eq hP]
  simp only [Submodule.subtype_apply, Submodule.coe_sum]

end GlobalTheory.CompanionTheory.WordFam
end
end

section

noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgTorus

open PositivityTheory.RgDs.K

variable {n : ℕ}

theorem tor_inv (θ : Fin n → ℝ) :
    (tor θ)⁻¹ = Matrix.diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
  apply Matrix.inv_eq_left_inv
  simp only [tor, Matrix.diagonal_mul_diagonal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  exact Matrix.diagonal_one

theorem adC_tor_ne (θ : Fin n → ℝ) {p q : Fin n × Fin n} (h : p ≠ q) : adC (tor θ) p q = 0 := by
  unfold adC
  rw [tor_inv]
  by_cases h1 : q.1 = p.1
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1.symm h2)
    rw [Matrix.diagonal_apply_ne _ h2, mul_zero]
  · unfold tor
    rw [Matrix.diagonal_apply_ne _ h1, zero_mul]

theorem adC_tor_self (θ : Fin n → ℝ) (p : Fin n × Fin n) :
    adC (tor θ) p p = Complex.exp (((θ p.1 - θ p.2 : ℝ) : ℂ) * Complex.I) := by
  unfold adC
  rw [tor_inv]
  unfold tor
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rhoTorus : RhoTorus := by
  intro n ε Λ T m θ k hk a x
  unfold rhoA
  rw [hk, Finset.sum_eq_single x.2]
  · congr 1
    simp only [adC_tor_self]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  · intro w _ hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (adC_tor_ne θ hi), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.RgTorus
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu

namespace GlobalTheory.CompanionTheory.SegLayers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun a b h =>
  Fin.ext ((IrrGL.nu_natCast_inj (x := Δ.first) Δ.d_pos).1 h)

theorem ms_nodup (Δ : Segment k) : Δ.ms.Nodup :=
  Multiset.Nodup.map (term_injective Δ) Finset.univ.nodup

theorem ncard_carrier (Δ : Segment k) : Δ.carrier.ncard = Δ.len := by
  rw [Segment.carrier, ← Set.image_univ, Set.ncard_image_of_injective _ (term_injective Δ)]
  simp

theorem ms_le {Δ : Segment k} {s : Multiset (IrrGL (k := k))} (h : ∀ x ∈ Δ.carrier, x ∈ s) : Δ.ms ≤ s :=
  (Multiset.le_iff_subset (ms_nodup Δ)).2 fun _ hx => h _ (Segment.mem_ms.1 hx)

theorem exists_longest {s : Multiset (IrrGL (k := k))} {y : IrrGL (k := k)} (hy : y ∈ s) (hc : y.IsCusp) :
    ∃ Γ : Segment k, (∀ x ∈ Γ.carrier, x ∈ s) ∧
      ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len := by
  classical
  let P : ℕ → Prop := fun l => ∃ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) ∧ D.len = l
  have hb : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Multiset.card s := fun D hD => by
    rw [← Segment.card_ms]
    exact Multiset.card_le_card (ms_le hD)
  have h1 : P 1 := ⟨Segment.single y hc, fun x hx => by
    rw [Segment.carrier_single] at hx
    exact hx ▸ hy, rfl⟩
  have h1' : 1 ≤ Multiset.card s := by
    obtain ⟨D, hD, e⟩ := h1
    exact e ▸ hb D hD
  obtain ⟨Γ, hΓ, e⟩ := Nat.findGreatest_spec h1' h1
  exact ⟨Γ, hΓ, fun D hD => e ▸ Nat.le_findGreatest (hb D hD) ⟨D, hD, rfl⟩⟩

theorem not_linked_of_longest {s : Multiset (IrrGL (k := k))} {Γ D : Segment k} (hΓ : ∀ x ∈ Γ.carrier, x ∈ s)
    (hm : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len) (hD : ∀ x ∈ D.carrier, x ∈ s) :
    ¬ Γ.Linked D := by
  rintro ⟨⟨U, hU⟩, -, h2⟩
  have h3 : U.len ≤ Γ.len := hm U fun x hx => by
    rw [hU] at hx
    exact hx.elim (hΓ x) (hD x)
  have h4 : Γ.carrier ⊂ U.carrier := by
    rw [hU]
    exact ⟨Set.subset_union_left, fun h => h2 (Set.subset_union_right.trans h)⟩
  have h5 := Set.ncard_lt_ncard h4 (Set.finite_range U.term)
  rw [ncard_carrier, ncard_carrier] at h5
  omega

theorem exists_unlinked (n : ℕ) : ∀ s : Multiset (IrrGL (k := k)), Multiset.card s = n → (∀ y ∈ s, y.IsCusp) →
    ∃ m : Multiset (Segment k), (∀ D ∈ m, ∀ D' ∈ m, ¬ D.Linked D') ∧ m.bind Segment.ms = s := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    rcases Multiset.empty_or_exists_mem s with rfl | ⟨y, hy⟩
    · exact ⟨0, by simp, by simp⟩
    obtain ⟨Γ, hΓ, hm⟩ := exists_longest hy (hs y hy)
    have hle := ms_le hΓ
    have hsub : ∀ x ∈ s - Γ.ms, x ∈ s := fun x hx => Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    have hcard : Multiset.card (s - Γ.ms) < n := by
      have h1 := Multiset.card_sub hle
      have h2 := Multiset.card_le_card hle
      have h3 := Γ.len_pos
      rw [Segment.card_ms] at h1 h2
      omega
    obtain ⟨m, hu, hb⟩ := ih _ hcard _ rfl fun x hx => hs x (hsub x hx)
    have hin : ∀ D ∈ m, ∀ x ∈ D.carrier, x ∈ s := fun D hD x hx =>
      hsub x (hb ▸ Multiset.mem_bind.2 ⟨D, hD, Segment.mem_ms.2 hx⟩)
    have hΓD : ∀ D ∈ m, ¬ Γ.Linked D := fun D hD => not_linked_of_longest hΓ hm (hin D hD)
    refine ⟨Γ ::ₘ m, fun D hD D' hD' => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hD with e | e₁ <;> rcases Multiset.mem_cons.1 hD' with e' | e₂
      · rw [e, e']
        exact Segment.not_linked_self _
      · rw [e]
        exact hΓD _ e₂
      · rw [e']
        exact fun h => hΓD _ e₁ h.symm
      · exact hu _ e₁ _ e₂
    · rw [Multiset.cons_bind, hb]
      exact add_tsub_cancel_of_le hle

theorem unlinkedLayers (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    UnlinkedLayers k := by
  intro s hs
  obtain ⟨m, hu, hb⟩ := exists_unlinked _ s rfl hs
  have hmem : ∀ i : Fin m.toList.length, m.toList.get i ∈ m := fun i =>
    Multiset.mem_toList.1 (List.get_mem _ _)
  refine ⟨m.toList.length, m.toList.get, fun i j _ => hu _ (hmem i) _ (hmem j), ?_⟩
  have h1 : (Finset.univ.val.map m.toList.get : Multiset (Segment k)) = m := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  conv_rhs => rw [← hb, ← h1]
  simp [Multiset.bind, Multiset.map_map, Function.comp_def]

end GlobalTheory.CompanionTheory.SegLayers

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem dpow_add_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s s' : ℝ) (x : GL (Fin n) k) : dpow n (s + s') x = dpow n s x * dpow n s' x := by
  simp only [dpow, detChar_apply, Complex.ofReal_add, absPow_add, MonoidHom.mul_apply]

theorem giso_tw_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  intro k _ _ _ _ n A s s'
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A.V) fun x => ?_⟩
  ext v
  show ((dpow n s' x : ℂˣ) : ℂ) • ((dpow n s x : ℂˣ) : ℂ) • A.ρ x v = ((dpow n (s + s') x : ℂˣ) : ℂ) • A.ρ x v
  rw [dpow_add_apply, smul_smul, Units.val_mul, mul_comm]

end GlobalTheory.CompanionTheory.LeibOrd

end
end
