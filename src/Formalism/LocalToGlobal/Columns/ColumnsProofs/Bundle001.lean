module

public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin
public import Formalism.LocalToGlobal.Columns.HeckeSp
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

section

open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Poly

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]

def HeckePolyFor (op : I → Module.End K V) (p : K[X]) : Prop :=
  p ≠ 0 ∧ ∃ s : Finset I, (∀ x, ∃ c : I → K, op x = ∑ y ∈ s, c y • op y) ∧ ∀ y ∈ s, Polynomial.aeval (op y) p = 0

theorem hfs_exists_poly [FiniteDimensional K V] (op : I → Module.End K V) : ∃ p, HeckePolyFor op p := by
  classical
  obtain ⟨b, hbsub, hbsp, hbli⟩ := exists_linearIndependent K (Set.range op)
  have hbfin : b.Finite := by
    first
    | exact hbli.setFinite
    | exact @Set.toFinite _ b hbli.finite
  obtain ⟨s, -, hs⟩ := Finset.subset_set_image_iff.1
    (show (↑hbfin.toFinset : Set (Module.End K V)) ⊆ op '' Set.univ by
      rw [Set.image_univ, Set.Finite.coe_toFinset]; exact hbsub)
  have h1 : ∀ x, op x ∈ Submodule.span K (op '' (s : Set I)) := by
    intro x
    rw [← Finset.coe_image, hs, Set.Finite.coe_toFinset, hbsp]
    exact Submodule.subset_span ⟨x, rfl⟩
  refine ⟨∏ y ∈ s, minpoly K (op y), ?_, s, fun x => ?_, fun y hy => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 (fun y _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral (op y)))
  · obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination K).1 (h1 x)
    refine ⟨l, ?_⟩
    rw [← hlx, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l (fun i hi => hl hi) _ (fun i _ => zero_smul K (op i))]
  · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun y => minpoly K (op y)) hy
    rw [hr, map_mul, minpoly.aeval, zero_mul]

end Poly

section Lifts

variable {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
  {S : GSD K} {S' : GSD L} (b : GSDBC ι S S')

namespace GSDBC

def Lifts (A' : Module.End L S'.EqFun) (A : Module.End K S.EqFun) : Prop := ∀ φ, A' (b.lift φ) = b.lift (A φ)

variable {b}

theorem Lifts.add {A' B' : Module.End L S'.EqFun} {A B : Module.End K S.EqFun} (hA : b.Lifts A' A) (hB : b.Lifts B' B) :
    b.Lifts (A' + B') (A + B) := by
  intro φ
  rw [LinearMap.add_apply, LinearMap.add_apply, hA φ, hB φ, lift_add]

theorem Lifts.sub {A' B' : Module.End L S'.EqFun} {A B : Module.End K S.EqFun} (hA : b.Lifts A' A) (hB : b.Lifts B' B) :
    b.Lifts (A' - B') (A - B) := by
  intro φ
  have hs : ∀ φ ψ : S.EqFun, b.lift (φ - ψ) = b.lift φ - b.lift ψ := fun φ ψ =>
    eq_sub_of_add_eq (by rw [← lift_add, sub_add_cancel])
  rw [LinearMap.sub_apply, LinearMap.sub_apply, hA φ, hB φ, hs]

theorem Lifts.mul {A' B' : Module.End L S'.EqFun} {A B : Module.End K S.EqFun} (hA : b.Lifts A' A) (hB : b.Lifts B' B) :
    b.Lifts (A' * B') (A * B) := by
  intro φ
  show A' (B' (b.lift φ)) = b.lift (A (B φ))
  rw [hB φ, hA]

theorem Lifts.smul {A' : Module.End L S'.EqFun} {A : Module.End K S.EqFun} (hA : b.Lifts A' A) (a : K) :
    b.Lifts (ι a • A') (a • A) := by
  intro φ
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hA φ, lift_smul]

theorem Lifts.one : b.Lifts 1 1 := fun _ => rfl

theorem Lifts.zero : b.Lifts 0 0 := by
  intro φ
  simp only [LinearMap.zero_apply, lift_zero]

theorem Lifts.pow {A' : Module.End L S'.EqFun} {A : Module.End K S.EqFun} (hA : b.Lifts A' A) (k : ℕ) :
    b.Lifts (A' ^ k) (A ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact Lifts.one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hA

theorem Lifts.sum {α : Type} (s : Finset α) (c : α → K) {A' : α → Module.End L S'.EqFun} {A : α → Module.End K S.EqFun}
    (hA : ∀ x ∈ s, b.Lifts (A' x) (A x)) : b.Lifts (∑ x ∈ s, ι (c x) • A' x) (∑ x ∈ s, c x • A x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lifts.zero
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact ((hA x (Finset.mem_insert_self x s)).smul (c x)).add
      (ih (fun y hy => hA y (Finset.mem_insert_of_mem hy)))

theorem Lifts.aeval {A' : Module.End L S'.EqFun} {A : Module.End K S.EqFun} (hA : b.Lifts A' A) (p : K[X]) :
    b.Lifts (Polynomial.aeval A' (p.map ι)) (Polynomial.aeval A p) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Polynomial.natDegree_map]
  simp only [Polynomial.coeff_map]
  exact Lifts.sum _ _ (fun i _ => hA.pow i)

variable (b)

theorem Lifts.eq_zero (F : CoefFrame ι) {A' : Module.End L S'.EqFun} (hA : b.Lifts A' 0) : A' = 0 := by
  refine LinearMap.ext_on (s := Set.range b.lift) ?_ ?_
  · exact eq_top_iff.2 (fun φ _ => mem_span_lift (b := b) (F := F) φ)
  · rintro _ ⟨φ, rfl⟩
    rw [hA φ]
    simp only [LinearMap.zero_apply, lift_zero]


include b in
theorem finiteDimensional (F : CoefFrame ι) [FiniteDimensional K S.EqFun] : FiniteDimensional L S'.EqFun := by
  classical
  let B := Module.finBasis K S.EqFun
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => b.lift (B i)) := by
    intro φ' _
    have h := mem_span_lift (b := b) (F := F) φ'
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨φ, rfl⟩
    rw [← B.sum_repr φ, lift_sum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  exact ⟨⟨Finset.univ.image fun i => b.lift (B i), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact eq_top_iff.2 hsp⟩⟩

theorem splitOver (F : CoefFrame ι) [FiniteDimensional K S.EqFun] {I : Type} (op : I → Module.End K S.EqFun)
    (op' : I → Module.End L S'.EqFun) (hl : ∀ x, b.Lifts (op' x) (op x)) (hc : PairComm op) {p : K[X]}
    (hp : HeckePolyFor op p) (hsp : (p.map ι).Splits) : SplitOver op' := by
  haveI := b.finiteDimensional F
  obtain ⟨hp0, s, hs, hd⟩ := hp
  have hcomm : ∀ y z, Commute (op' y) (op' z) := fun y z => by
    have h0 : b.Lifts (op' y * op' z - op' z * op' y) 0 := by
      have := ((hl y).mul (hl z)).sub ((hl z).mul (hl y))
      rwa [(hc y z).eq, sub_self] at this
    exact sub_eq_zero.mp (Lifts.eq_zero b F h0)
  have hsplit : ∀ y ∈ s, ⨆ μ, (op' y).maxGenEigenspace μ = ⊤ := by
    intro y hy
    apply hfs_iSup_maxGen_of_splits
    have h0 : b.Lifts (Polynomial.aeval (op' y) (p.map ι)) 0 := by
      have := (hl y).aeval p
      rwa [hd y hy] at this
    have hann : Polynomial.aeval (op' y) (p.map ι) = 0 := Lifts.eq_zero b F h0
    exact hsp.of_dvd (Polynomial.map_ne_zero hp0) (minpoly.dvd L _ hann)
  intro x
  obtain ⟨c, hcx⟩ := hs x
  have h0 : b.Lifts (op' x - ∑ y ∈ s, ι (c y) • op' y) 0 := by
    have := (hl x).sub (Lifts.sum (b := b) s c fun y _ => hl y)
    rwa [← hcx, sub_self] at this
  have hx : op' x = ∑ y ∈ s, ι (c y) • op' y := sub_eq_zero.mp (Lifts.eq_zero b F h0)
  rw [hx]
  exact hfs_iSup_maxGen_sum s op' (fun y => ι (c y)) (fun y _ z _ => hcomm y z) hsplit

end GSDBC

end Lifts

section HeckeLift

variable {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
  {S : GSD K} {S' : GSD L} (b : GSDBC ι S S')
  {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (c : DecoPts S E n ST SG) (c' : DecoPts S' E n ST SG)

namespace GSDBC

end GSDBC

end HeckeLift

end Formalism.L2.Col
end
end

section

open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section VVMap

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_blockEmb (s : σ) (f : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial.map ι (Formalism.GradedWeylDivisibility.blockEmb K s f) = Formalism.GradedWeylDivisibility.blockEmb L s (MvPolynomial.map ι f) := by
  unfold Formalism.GradedWeylDivisibility.blockEmb
  exact MvPolynomial.map_rename _ _ _

private lemma map_aeval_eq_aeval_map' {α β : Type} (g : α → MvPolynomial β K) (g' : α → MvPolynomial β L)
    (hg : ∀ v, MvPolynomial.map ι (g v) = g' v) (F : MvPolynomial α K) :
    MvPolynomial.map ι (MvPolynomial.aeval g F) = MvPolynomial.aeval g' (MvPolynomial.map ι F) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, hp, hg]

private lemma map_mem_dualWeyl' {r m : ℕ} {ν : Fin m → ℕ} {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r m ν) : MvPolynomial.map ι f ∈ Formalism.GradedWeylDivisibility.dualWeyl L r m ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  constructor
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    rw [MvPolynomial.coeff_map] at hd
    intro h0
    apply hd
    rw [h0, map_zero]
  · simp only [Submodule.mem_iInf] at h2 ⊢
    intro l j hlj
    have h3 := h2 l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h3 ⊢
    simp only [AlgHom.toLinearMap_apply] at h3 ⊢
    rw [← MvPolynomial.map_rename, ← h3]
    unfold Formalism.GradedWeylDivisibility.colAddGen
    refine (map_aeval_eq_aeval_map' ι _ _ (fun v => ?_) f).symm
    split_ifs <;> simp

theorem hfs_map_mem_VV {F : Pol K σ n} (hF : F ∈ VV K lam) : MvPolynomial.map ι F ∈ VV L lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => MvPolynomial.map ι (G s), fun s => ?_, ?_⟩
    · have h1 : G s ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n (lam s).natW := hG s
      exact map_mem_dualWeyl' ι h1
    · rw [map_prod]
      exact Finset.prod_congr rfl fun s _ => hfs_map_blockEmb ι s (G s)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

def hfsJ : VV K lam →+ VV L lam where
  toFun v := ⟨MvPolynomial.map ι (v : Pol K σ n), hfs_map_mem_VV ι lam v.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' v w := Subtype.ext (map_add _ _ _)

theorem hfsJ_coe (v : VV K lam) : ((hfsJ ι lam v : VV L lam) : Pol L σ n) = MvPolynomial.map ι (v : Pol K σ n) := rfl

theorem hfsJ_smul (a : K) (v : VV K lam) : hfsJ ι lam (a • v) = ι a • hfsJ ι lam v := by
  apply Subtype.ext
  rw [hfsJ_coe, Submodule.coe_smul, Submodule.coe_smul, hfsJ_coe, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem hfsJ_li (F : CoefFrame ι) : LinearIndependent L fun i => hfsJ ι lam (bVV K lam i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hpol : ∑ j ∈ s, g j • MvPolynomial.map ι ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    have h0 := congrArg (fun v : VV L lam => (v : Pol L σ n)) hg
    simpa [hfsJ_coe] using h0
  have hK : ∀ k, ∑ j ∈ s, F.c (g j) k • ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    intro k
    ext d
    have h1 := congrArg (AddMonoidAlgebra.coeff · d) hpol
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1 ⊢
    have h2 := congrArg (fun y => F.c y k) h1

    simp only [map_sum, map_zero, Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), F.smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hli := (bVV K lam).linearIndependent
  rw [linearIndependent_iff'] at hli
  have hz : ∀ k, F.c (g i) k = 0 := by
    intro k
    refine hli s (fun j => F.c (g j) k) ?_ i hi
    apply Subtype.ext
    simpa using hK k
  rw [F.spec (g i)]
  simp [hz]

theorem hfsJ_span (F : CoefFrame ι) : ⊤ ≤ Submodule.span L (Set.range fun i => hfsJ ι lam (bVV K lam i)) := by
  classical
  haveI : FiniteDimensional L (VV L lam) := Module.Basis.finiteDimensional_of_finite (bVV L lam)
  rw [(hfsJ_li ι lam F).span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis (bVV L lam)).symm]

end VVMap

section Act

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_trAct (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (trAct g F) = trAct (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold trAct Formalism.GradedWeylDivisibility.blockAct
  refine map_aeval_eq_aeval_map' ι _ _ (fun v => ?_) F

  simp [map_sum, Formalism.UG.bc, Matrix.transpose_apply]

theorem hfs_detPow_bc (g : GL (Fin n) K) (c : ℤ) : detPow L n (Formalism.UG.bc ι g) c = ι (detPow K n g c) := by
  unfold detPow
  have h : Matrix.GeneralLinearGroup.det (Formalism.UG.bc ι g) =
      Units.map (ι : K →* L) (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [h, ← map_zpow, Units.coe_map]
  rfl

theorem hfs_detTwK_bc (g : σ → GL (Fin n) K) : detTwK lam (fun τ => Formalism.UG.bc ι (g τ)) = ι (detTwK lam g) := by
  unfold detTwK
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => hfs_detPow_bc ι (g τ) _

theorem hfs_map_actP (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (actP lam g F) = actP lam (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold actP
  rw [LinearMap.smul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hfs_map_trAct,
    hfs_detTwK_bc]

theorem hfs_rhoK (g : σ → GL (Fin n) K) (v : VV K lam) :
    rhoK lam (fun τ => Formalism.UG.bc ι (g τ)) (hfsJ ι lam v) = hfsJ ι lam (rhoK lam g v) := by
  apply Subtype.ext
  show actP lam (fun τ => Formalism.UG.bc ι (g τ)) ((hfsJ ι lam v : VV L lam) : Pol L σ n) =
    MvPolynomial.map ι (actP lam g (v : Pol K σ n))
  rw [hfsJ_coe, hfs_map_actP]

variable [NumberField K] [NumberField L] {E : Type} [Field E] [NumberField E]

theorem hfs_embGL (emb : σ → E →+* K) (γ : GL (Fin n) E) :
    embGL (fun τ => ι.comp (emb τ)) γ = fun τ => Formalism.UG.bc ι (embGL emb γ τ) := by
  funext τ
  apply Units.ext
  ext i j
  simp [embGL, Formalism.UG.bc]

theorem hfs_invTrK (g : σ → GL (Fin n) K) : invTrK (fun τ => Formalism.UG.bc ι (g τ)) = fun τ => Formalism.UG.bc ι (invTrK g τ) := by
  funext τ
  apply Units.ext
  show ((((Formalism.UG.bc ι (g τ))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).transpose =
    ((Formalism.UG.bc ι (inside₂ K n (g τ)) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [← map_inv]
  ext i j
  simp [Formalism.UG.bc, inside₂]

theorem hfs_rhoV (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoV (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoV emb lam γ v) := by
  show rhoK lam (embGL (fun τ => ι.comp (emb τ)) γ) (hfsJ ι lam v) = hfsJ ι lam (rhoK lam (embGL emb γ) v)
  rw [hfs_embGL]
  exact hfs_rhoK ι lam _ v

theorem hfs_rhoVr (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoVr (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoVr emb lam γ v) := by
  show rhoK lam (invTrK (embGL (fun τ => ι.comp (emb τ)) γ)) (hfsJ ι lam v) =
    hfsJ ι lam (rhoK lam (invTrK (embGL emb γ)) v)
  rw [hfs_embGL, hfs_invTrK]
  exact hfs_rhoK ι lam _ v

end Act

end Formalism.L2.Col
end
end
