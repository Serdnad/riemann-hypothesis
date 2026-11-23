module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

open NumberField Neutral.B1 GlobalTheory.HeckeGal
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charInj_holds :
    CharInj := by
  intro E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'
  have hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  have hfin := Ideal.finite_factors hl
  have hquot : χ * χ'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (χ * χ'⁻¹).1
      (χ * χ'⁻¹).2.1 (χ * χ'⁻¹).2.2 hfin.toFinset fun v hv x => ?_)
    have hl' : (l : 𝓞 E) ∉ v.asIdeal :=
      fun h => hv (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr h))
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v x))
    have a := hχ.loc_away (Or.inl hl') x σ hσ.symm
    have b := hχ'.loc_away (Or.inl hl') x σ hσ.symm
    have hloc : χ.loc v x = χ'.loc v x :=
      Units.ext (ι.symm.injective (a.symm.trans b))
    change χ.loc v x * (χ'.loc v x)⁻¹ = 1
    rw [hloc, mul_inv_cancel]
  exact mul_inv_eq_one.mp hquot
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G IsPlaceOver
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

namespace UpperTheory.Gal.TP.Sub.PFrobSub

private theorem prod_scale {K : Type} [Field K] {c : K} (hc : c ≠ 0) (x : K) (S : Multiset K) :
    c ^ Multiset.card S * (S.map fun z => x / c - z).prod = (S.map fun z => x - z * c).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have e : c * (x / c - a) = x - a * c := by
      field_simp
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ← ih, ← e]
    ring

private theorem charpoly_smul_eq {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) (S : Multiset K) (h : M.charpoly = (S.map fun z => X - C z).prod) :
    (c • M).charpoly = (S.map fun z => X - C (z * c)).prod := by
  apply Polynomial.funext
  intro x
  have hn : Multiset.card S = n := by
    have := congrArg Polynomial.natDegree h
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have key : Matrix.scalar (Fin n) x - c • M = c • (Matrix.scalar (Fin n) (x / c) - M) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs <;> field_simp
  rw [Matrix.eval_charpoly, key, Matrix.det_smul, ← Matrix.eval_charpoly, h, Fintype.card_fin, ← hn,
    Polynomial.eval_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact prod_scale hc x S

private theorem sumRep_left {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom]
  rfl

private theorem characterAsRankOneRep_entry {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) (g : Γ) :
    (rk1 μ g : Matrix (Fin 1) (Fin 1) k) 0 0 = (μ g : k) := by
  unfold rk1
  simp

end UpperTheory.Gal.TP.Sub.PFrobSub

open UpperTheory.Gal.TP.Sub.PFrobSub in
theorem UpperTheory.Gal.TP.Sub.frobSub_holds :
    CpFacts → FrobSub := by
  intro h E Ω _ _ _ _ _ l _ ι a w S c μ hμ
  have hc : ∀ A, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
      ι.toRingHom (μ σ⁻¹ : Qbar l) = c := by
    intro A hA σ hσ
    have h1 := (hμ A hA).2 σ hσ
    have h2 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
    unfold cp at h2
    rw [h2] at h1
    simpa using h1
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e := hI σ hσ
      ext i j
      have hij := sumRep_left s (rk1 μ) σ i j
      rw [e] at hij
      rw [← hij]
      simp [Matrix.one_apply]
    · have e := hF σ hσ
      have h3 := (h (G E Ω) (Qbar l) a 1).1 s (rk1 μ) σ⁻¹
      have h4 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
      unfold cp at h3 h4
      rw [h3, Polynomial.map_mul, h4] at e
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
      rw [hc A hA σ hσ, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_singleton,
        Multiset.prod_singleton] at e
      exact mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero c) e
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    obtain ⟨hIμ, -⟩ := hμ A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e1 := hI σ hσ
      have e2 : (μ σ : Qbar l) = 1 := by
        rw [← characterAsRankOneRep_entry μ σ, hIμ σ hσ]
        simp
      ext i j
      rw [UpperTheory.V.Af.tw_val, e1, e2]
      simp
    · have e := hF σ hσ
      have hc' := hc A hA σ hσ
      have hc0 : c ≠ 0 := by
        rw [← hc']
        simp
      rw [UpperTheory.V.Af.tw_val, ← Matrix.charpoly_map]
      rw [← Matrix.charpoly_map] at e
      have hm : ((μ σ⁻¹ : Qbar l) • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l))).map ι.toRingHom =
          c • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom := by
        rw [← hc']
        ext i j
        simp
      rw [hm, Multiset.map_map]
      exact charpoly_smul_eq _ hc0 S e
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

noncomputable section

namespace UpperTheory.Gal.TP.Sub

section SplitLineAux

variable {Γ k : Type} [Group Γ] [Field k] {m : ℕ}

private lemma sumRep_val (s : Γ →* GL (Fin m) k) (c : Γ →* kˣ) (g : Γ) :
    ((sumRep s (rk1 c) g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      (Matrix.fromBlocks (s g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private lemma rankOneRep_val (c : Γ →* kˣ) (g : Γ) (i j : Fin 1) :
    ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) i j = (c g : k) := by
  simp [rk1, Subsingleton.elim i j]

private def resHom (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (r (g * h) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k) =
      (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec
        ((r h : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') : Γ →* GL (Fin m) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix b b (resHom r hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }

private lemma subRep_val (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (g : Γ) :
    ((subRep r hinv b g : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      LinearMap.toMatrix b b (resHom r hinv g) := rfl

private def colM {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    (v : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin m ⊕ Fin 1) k :=
  Matrix.of fun i => Sum.elim (fun j => (b j : Fin (m + 1) → k) i) (fun _ => v i)

private lemma intertw (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (c : Γ →* kˣ) (v : Fin (m + 1) → k)
    (hv : ∀ g, (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v = (c g : k) • v) (g : Γ) :
    (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v =
      colM b v * Matrix.fromBlocks (subRep r hinv b g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) := by
  ext i j
  rcases j with j | j
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inl j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i := rfl
    have h2 := b.sum_repr (resHom r hinv g (b j))
    have h4 : ((resHom r hinv g (b j) : W') : Fin (m + 1) → k) =
        (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k) := rfl
    have h3 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i =
        ∑ a, (b.repr (resHom r hinv g (b j))) a * (b a : Fin (m + 1) → k) i := by
      have h5 := congrArg (fun u : W' => (u : Fin (m + 1) → k) i) h2
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at h5
      rw [← h4, h5]
    rw [h1, h3, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [subRep_val, colM, LinearMap.toMatrix_apply, mul_comm]
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inr j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v) i := rfl
    rw [h1, hv g, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [colM, rankOneRep_val, mul_comm]

private lemma col_indep {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    {v : Fin (m + 1) → k} (hv0 : v ≠ 0) (hc : IsCompl (Submodule.span k {v}) W') :
    LinearIndependent k (Sum.elim (fun j => (b j : Fin (m + 1) → k)) (fun _ : Fin 1 => v)) := by
  refine LinearIndependent.sum_type
    (b.linearIndependent.map' W'.subtype (Submodule.ker_subtype W'))
    (LinearIndependent.of_subsingleton (0 : Fin 1) hv0) ?_
  refine Disjoint.mono ?_ ?_ hc.disjoint.symm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (b j).2
  · rw [Set.range_const]

end SplitLineAux

end UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.splitLine_holds : SplitLine := by
  intro Γ k _ _ m r hss c ⟨v, hv0, hv⟩
  have hW : IsInv r (Submodule.span k {v}) := by
    intro g x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Matrix.mulVec_smul, hv g, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  obtain ⟨W', hinv, hc⟩ := hss _ hW
  have hfr : Module.finrank k W' = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_span_singleton hv0, Module.finrank_fin_fun] at h
    omega
  let b : Module.Basis (Fin m) k W' := Module.finBasisOfFinrankEq k W' hfr
  let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) k := (colM b v).submatrix id finSumFinEquiv.symm
  have hQ : IsUnit Q := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have := (col_indep b hv0 hc).comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    convert this using 1
    ext j i
    rcases h : finSumFinEquiv.symm j with j' | j' <;> simp [Q, colM, Matrix.col, h]
  obtain ⟨q, hq⟩ := hQ
  refine ⟨subRep r hinv b, q⁻¹, fun g => ?_⟩
  have key : (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * Q =
      Q * (sumRep (subRep r hinv b) (rk1 c) g : GL (Fin (m + 1)) k) := by
    rw [sumRep_val]
    change _ * (colM b v).submatrix id finSumFinEquiv.symm =
      (colM b v).submatrix id finSumFinEquiv.symm * _
    rw [Matrix.submatrix_mul_equiv, ← intertw r hinv b c v hv g]
    ext i j
    rfl
  have key2 : r g * q = q * sumRep (subRep r hinv b) (rk1 c) g := Units.ext (by
    simpa [hq] using key)
  rw [inv_inv, mul_assoc, key2, ← mul_assoc, inv_mul_cancel, one_mul]
end
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem univ_map_snoc {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) :
    Finset.univ.val.map f =
      Finset.univ.val.map (fun i : Fin t => f i.castSucc) + {f (Fin.last t)} := by
  rw [Fin.univ_castSuccEmb]
  simp [Finset.map_val, Multiset.map_map, add_comm, Function.comp_def]

theorem UpperTheory.Gal.TP.Sub.peelAll_holds :
    PeelOne → ContLeft → ClConj → ClSub → PeelAll := by
  intro hP hC hJ hS E Ω _ _ _ _ _ l _ ι n m' t' r' a' hr' t
  induction t with
  | zero =>
    intro r a hc hss _ _ _
    refine ⟨r, hc, hss, ?_⟩
    intro w S c J m _ h
    simpa using h
  | succ t ih =>
    intro r a hc hss ha hne hid
    obtain ⟨s₁, hs₁, hiso, hid₁⟩ :=
      hP (G E Ω) (Qbar l) (n + t) m' t t' r r' a a' hss hr' hne hid
    have hC' := hC (G E Ω) (Qbar l) (n + t) 1
    have hC1 := hC (G E Ω) (Qbar l) (n + t + 1) 1
    have hcl : Continuous (sumRep s₁ (rk1 (a (Fin.last t)))) := hC1.2.1 _ _ hiso hc
    have hcs₁ : Continuous s₁ := hC'.1 _ _ hcl
    obtain ⟨s, hsc, hss', hcl'⟩ := ih s₁ (fun i => a i.castSucc) hcs₁ hs₁
      (fun i => ha _) (fun i j => hne _ _) hid₁
    refine ⟨s, hsc, hss', ?_⟩
    intro w S c J m hcl0 h
    have h2 := hJ E Ω l ι _ r _ hc hiso w _ _ h
    refine hcl' w S (fun i => c i.castSucc) J (fun i => m i.castSucc) (fun i => hcl0 _) ?_
    refine hS E Ω l ι _ s₁ (a (Fin.last t)) hcs₁ (ha _) w _ (c (Fin.last t)) _
      (m (Fin.last t)) (hcl0 _) ?_
    have e1 : S + Finset.univ.val.map c =
        S + Finset.univ.val.map (fun i : Fin t => c i.castSucc) + {c (Fin.last t)} := by
      rw [univ_map_snoc c, add_assoc]
    have e2 : (fun τ => J τ + Finset.univ.val.map fun i => m i τ) =
        fun τ => J τ + Finset.univ.val.map (fun i : Fin t => m i.castSucc τ) +
          {m (Fin.last t) τ} := by
      funext τ
      rw [univ_map_snoc (fun i => m i τ), add_assoc]
    rw [e1, e2] at h2
    exact h2
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charEx_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → CharFrob → CharAbove → CharInj → CharEx := by
  classical
  intro H hF hA hI E Ω _ _ _ _ _ l _ ι
  obtain ⟨art, hart, hex⟩ := H E Ω
  have hL : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r :=
    fun χ n h => (hex l ι χ n h).exists
  let L : HChar E → ((E →+* ℂ) → ℤ) → (G E Ω →* (Qbar l)ˣ) :=
    fun χ n => if h : IsAlgPos χ n then (hL χ n h).choose else 1
  have hspec : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      Continuous (L χ n) ∧ IsLAdicOf art ι χ n (L χ n) := by
    intro χ n h
    have e : L χ n = (hL χ n h).choose := dif_pos h
    rw [e]
    exact (hL χ n h).choose_spec
  refine ⟨L, fun χ n h => ⟨(hspec χ n h).1, fun w hw => ⟨fun hl => ?_, ?_⟩⟩, fun χ n χ' n' h h' e => ?_⟩
  · exact hF E Ω l ι art hart χ n (L χ n) (hspec χ n h).2 w hl hw
  · exact hA E Ω l ι art hart χ n (L χ n) h (hspec χ n h).1 (hspec χ n h).2 w hw
  · exact hI E Ω l ι art hart χ χ' n n' (L χ n) (hspec χ n h).2 (e ▸ (hspec χ' n' h').2)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clAway_holds :
    ClAway := by
  intro E Ω _ _ _ _ _ l _ ι a r w hl S J
  refine ⟨fun h => h.1 hl, fun h => ⟨fun _ => h, ?_⟩⟩
  intro P AI _ A hA O _ _ _ Bw hj
  exact absurd (hj.mem_placesOver hA) hl
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.pstOfDR_holds :
    GlobalTheory.Published.DeRhamPotSemistable → PstOfDR := by
  intro hB l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r hr hd
  obtain ⟨T⟩ := hT
  exact hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem charFrob_holds : CharFrob := by
  intro E Ω _ _ _ _ _ l _ ι art ha χ n μ h w hw hu A hA
  have hv : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∨ n = 0 := Or.inl hw
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : μ s = 1 := (h.unr_iff ha hv hA).mpr hu s hs
    simp [rk1, h1]
  · have h1 : ((μ σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val w : ℂˣ) : ℂ))⁻¹ := h.frob_unr ha hv hu hA hσ
    simp [rk1, Matrix.charpoly, Matrix.det_fin_one, h1, Polynomial.map_sub]

end UpperTheory.Gal.TP.Sub

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open Neutral.B1 hiding Dec
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw tw_val)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem twJumps_holds : TwJumps := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r c _ _ τ J m h1 h2
  exact (GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a r (tw r c) c
    (fun g => tw_val r c g)).2.2.2 τ J m h1 h2

end UpperTheory.Gal.TP.Sub

end
end
