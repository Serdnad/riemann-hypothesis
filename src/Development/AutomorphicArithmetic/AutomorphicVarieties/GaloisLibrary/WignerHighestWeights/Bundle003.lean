module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.holEq :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (x : Matrix (Fin a) (Fin a) ℂ),
      hol τ L x = (1 / 2 : ℂ) • (L (toL (x.map (atEmb τ))) - Complex.I • L (toL ((Complex.I • x).map (atEmb τ)))) := by
  intro E _ _ _ a N _ _ _ _ τ L x
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  have hsum : ∀ y : Matrix (Fin a) (Fin a) ℂ,
      L' (y.map (atEmb τ)) = ∑ i, ∑ j, L' (Matrix.single i j (atEmb τ (y i j))) := fun y => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (y.map (atEmb τ))]

    simp only [map_sum, Matrix.map_apply]
  have hL : ∀ (i j : Fin a) (w : ℂ), L' (Matrix.single i j (atEmb τ w)) =
      (w.re : ℂ) • L' (Matrix.single i j (atEmb τ 1)) +
        (w.im : ℂ) • L' (Matrix.single i j (atEmb τ Complex.I)) := fun i j w => by
    rw [atEmb_eq τ w, Matrix.single_add, ← Matrix.smul_single, ← Matrix.smul_single, map_add (f := _), map_smul, map_smul,
      ← algebraMap_smul ℂ w.re, ← algebraMap_smul ℂ w.im]
    rfl
  change ∑ i, ∑ j, x i j • ((1 / 2 : ℂ) • (L' (Matrix.single i j (atEmb τ 1)) -
      Complex.I • L' (Matrix.single i j (atEmb τ Complex.I)))) =
    (1 / 2 : ℂ) • (L' (x.map (atEmb τ)) - Complex.I • L' ((Complex.I • x).map (atEmb τ)))
  rw [hsum, hsum]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, hL i j (x i j), hL i j (Complex.I * x i j)]
  generalize x i j = c
  conv_lhs => rw [← Complex.re_add_im c]
  simp only [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination (-(c.im : ℂ) / 2) * Complex.I_mul_I
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rpDer {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (D : Module.End ℂ M) (g : X → X) (n : ℕ) :
    ∀ (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, D * b i y - b i y * D = b i (g y)) → ∀ x : Fin n → X,
      D * rp n b x = rp n b x * D + ∑ k, rp n b (Function.update x k (g (x k))) := by
  induction n with
  | zero => intro b _ x; simp [rp_zero]
  | succ n ih =>
    intro b hb x
    have h1 := ih (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : D * b 0 (x 0) = b 0 (x 0) * D + b 0 (g (x 0)) := by rw [← hb]; abel
    rw [Fin.sum_univ_succ]
    simp only [rp_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← mul_assoc, h1, add_mul, mul_assoc, h0, Finset.sum_mul, mul_add, mul_assoc, add_assoc]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telDer :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (D : Module.End ℂ M) (g : X → X),
      (∀ i y, D * a i y - a i y * D = a i (g y)) → (∀ i y, D * b i y - b i y * D = b i (g y)) →
      ∀ f f' : X →ₗ[ℂ] M, (∀ y, D (f y) = f' y + f (g y)) → ∀ x : Fin n → X,
        D (tel n a b f x) = tel n a b f' x + ∑ k, tel n a b f (Function.update x k (g (x k))) := by
  intro X M _ _ _ _ n
  induction n with
  | zero => intro a b D g _ _ f f' _ x; simp [tel_zero]
  | succ n ih =>
    intro a b D g ha hb f f' hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) D g (fun i y => ha i.succ y) (fun i y => hb i.succ y) f f' hf (Fin.tail x)
    have h2 := rpDer D g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : ∀ m, D (a 0 (x 0) m) = a 0 (x 0) (D m) + a 0 (g (x 0)) m := by
      intro m
      rw [← ha]
      simp
    have h3 : ∀ m, D (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (D m) +
        ∑ k : Fin n, rp n (Fin.tail b) (Function.update (Fin.tail x) k (g (x k.succ))) m := by
      intro m
      have := LinearMap.congr_fun h2 m
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply] at this
      exact this
    have h4 : D (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x)) = tel n (Fin.tail a) (Fin.tail b) f' (Fin.tail x) +
        ∑ k : Fin n, tel n (Fin.tail a) (Fin.tail b) f (Function.update (Fin.tail x) k (g (x k.succ))) := h1
    rw [Fin.sum_univ_succ]
    simp only [tel_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]

    rw [map_add (f := _), h0, h3, h4, hf, map_add (f := _), map_add (f := _), map_sum, Finset.sum_add_distrib]
    abel
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.tensDer :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), SepDer (tensorK π Ξ) (tensorLie π Ξ) := by
  intro E _ _ _ a π Ξ k Z h0 hk m' hm
  let e := TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d)
  have h1 : e m' ≠ 0 := fun h => hm (e.map_eq_zero_iff.1 h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
  have h2 : (e m' j).1.1 ≠ 0 := fun h => hj (Subtype.ext (Subtype.ext h))
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : π.V ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (e m j).1.1 g
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : π.V) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1.1 g * v j := fun φ v => by
    have h : e (φ ⊗ₜ v) j = v j • φ := by
      simp only [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    change (e (φ ⊗ₜ v) j).1.1 g = _
    rw [h, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    simp only [tensorK, tensorLie_tmul, TensorProduct.map_tmul, map_add (f := _), hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem weight_operator_commutator_multiGl {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (F : ι → Fin n → Fin n → Module.End ℂ V) (hF : IsMultiGl F) (t : ι) (i j : Fin n) (x : V) :
    (∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) (F t i j x) =
      F t i j ((∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) x) +
        (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) • F t i j x := by
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have key : ∀ s (a : Fin n), F s a a (F t i j x) = F t i j (F s a a x) +
      (if s = t then ((if a = i then F t a j x else 0) - (if j = a then F t i a x else 0)) else 0) := by
    intro s a
    by_cases hst : s = t
    · subst hst
      rw [if_pos rfl]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hgl s a a i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h2 : (if a = i then F s a j x else 0) - (if j = a then F s i a x else 0) =
          (if a = i then F s a j else 0) x - (if j = a then F s i a else 0) x := by
        split_ifs <;> simp
      rw [h2, ← h1]
      abel
    · rw [if_neg hst]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hcomm s t hst a a i j)
      simp only [Module.End.mul_apply] at h1
      rw [h1, add_zero]

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_add, Finset.sum_add_distrib,
  map_sum, map_smul]
  congr 1
  simp [smul_ite, smul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.sum_ite_irrel, sub_smul]

theorem UpperTheory.V.AlgRepEndIrreducible.lowLine :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V), IsMultiGl F → ∀ (ν : ι → Fin n → ℂ) (v : V), (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
      ∀ w ∈ low F v, (∀ t k, F t k k w = ν t k • w) → ∃ c : ℂ, w = c • v := by
  intro ι V _ _ _ n F hF ν v hv w hw hwν
  classical
  set H : Module.End ℂ V := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a with hH
  set l0 : ℂ := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) * ν s a with hl0
  have hHx : ∀ x : V, (∀ s k, F s k k x = ν s k • x) → H x = l0 • x := by
    intro x hx
    simp only [hH, hl0, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, Finset.sum_smul]
  have hsh : ∀ t (i j : Fin n) (μ : ℂ) (x : V), H x = μ • x →
      H (F t i j x) = (μ + (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ))) • F t i j x := by
    intro t i j μ x hx
    rw [hH, weight_operator_commutator_multiGl F hF t i j x, ← hH, hx, map_smul, add_smul]
  have hdist : ∀ i j : Fin n, j < i → ∃ d : ℕ, ((i : ℕ) : ℂ) - ((j : ℕ) : ℂ) = (d : ℂ) + 1 := by
    intro i j hji
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
    refine ⟨d, ?_⟩
    rw [hd]
    push_cast
    ring
  let M : Submodule ℂ V := ⨆ k : ℕ, H.eigenspace (l0 + ((k : ℂ) + 1))
  have hFM : ∀ t (i j : Fin n), j < i → ∀ z ∈ M, F t i j z ∈ M := by
    intro t i j hji z hz
    obtain ⟨d, hd⟩ := hdist i j hji
    refine Submodule.iSup_induction _ (motive := fun z => F t i j z ∈ M) hz ?_ ?_ ?_
    · intro k z hz
      rw [Module.End.mem_eigenspace_iff] at hz
      have h1 := hsh t i j _ z hz
      refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) (k + d + 1)) ?_
      rw [Module.End.mem_eigenspace_iff, h1, hd]
      congr 1
      push_cast
      ring
    · simp
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  let P : Submodule ℂ V := (ℂ ∙ v) ⊔ M
  have hvP : v ∈ P := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  have hPst : ∀ t (i j : Fin n), j < i → ∀ x ∈ P, F t i j x ∈ P := by
    intro t i j hji x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add (f := _), map_smul]
    refine Submodule.mem_sup_right (add_mem (Submodule.smul_mem _ _ ?_) (hFM t i j hji z hz))
    obtain ⟨d, hd⟩ := hdist i j hji
    refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) d) ?_
    rw [Module.End.mem_eigenspace_iff, hsh t i j l0 v (hHx v (fun s k => (hv s).1 k)), hd]
  have hle : low F v ≤ P := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    exact sInf_le ⟨hvP, hPst⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hHz : H z = l0 • z := by
    have e1 := hHx w hwν
    have e2 := hHx v (fun s k => (hv s).1 k)
    have e3 : z = w - c • v := by
      rw [← hyz]
      abel
    rw [e3, map_sub, map_smul, e1, e2, smul_sub, smul_comm]
  have hMle : M ≤ ⨆ μ, ⨆ (_ : μ ≠ l0), H.eigenspace μ := by
    refine iSup_le fun k => le_iSup₂_of_le (l0 + ((k : ℂ) + 1)) ?_ le_rfl
    intro h
    have h2 : ((k : ℂ) + 1) = 0 := by linear_combination h
    exact Nat.cast_add_one_ne_zero k h2
  have hz0 : z = 0 :=
    (Submodule.disjoint_def.mp ((Module.End.eigenspaces_iSupIndep H) l0)) z
      (Module.End.mem_eigenspace_iff.mpr hHz) (hMle hz)
  refine ⟨c, ?_⟩
  rw [← hyz, hz0, add_zero]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.lowStab :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V), IsMultiGl F → ∀ (ν : ι → Fin n → ℂ) (v : V), (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
      v ∈ low F v ∧ Stab F (low F v) := by
  intro ι V _ _ _ n F hF ν v hv
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have hvlow : v ∈ low F v := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    rw [Submodule.mem_sInf]
    intro p hp
    exact hp.1
  have hlow : ∀ t (i j : Fin n), j < i → ∀ w ∈ low F v, F t i j w ∈ low F v := by
    intro t i j hji w hw
    unfold UpperTheory.V.AlgRepEndIrreducible.low at hw ⊢
    rw [Submodule.mem_sInf] at hw ⊢
    intro p hp
    exact hp.2 t i j hji w (hw p hp)
  let W' : Submodule ℂ V := low F v ⊓ ⨅ t, ⨅ i, ⨅ j, (low F v).comap (F t i j)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ low F v ∧ ∀ t i j, F t i j w ∈ low F v := by
    intro w
    simp [W', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  have hvW : v ∈ W' := by
    rw [hmem]
    refine ⟨hvlow, fun t i j => ?_⟩
    rcases lt_trichotomy i j with h | h | h
    · rw [(hv t).2 i j h]
      exact zero_mem _
    · subst h
      rw [(hv t).1 i]
      exact Submodule.smul_mem _ _ hvlow
    · exact hlow t i j h v hvlow
  have hWst : ∀ t (k l : Fin n), l < k → ∀ w ∈ W', F t k l w ∈ W' := by
    intro t k l hlk w hw
    rw [hmem] at hw ⊢
    refine ⟨hlow t k l hlk w hw.1, fun s i j => ?_⟩
    by_cases hst : s = t
    · subst hst
      have h1 := congrArg (fun f : Module.End ℂ V => f w) (hgl s i j k l)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      refine add_mem (sub_mem ?_ ?_) (hlow s k l hlk _ (hw.2 s i j))
      · split_ifs
        · exact hw.2 s i l
        · rw [LinearMap.zero_apply]
          exact zero_mem _
      · split_ifs
        · exact hw.2 s k j
        · rw [LinearMap.zero_apply]
          exact zero_mem _
    · have h1 := congrArg (fun f : Module.End ℂ V => f w) (hcomm s t hst i j k l)
      simp only [Module.End.mul_apply] at h1
      rw [h1]
      exact hlow t k l hlk _ (hw.2 s i j)
  have hle : low F v ≤ W' := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    exact sInf_le ⟨hvW, hWst⟩
  exact ⟨hvlow, fun t i j w hw => ((hmem w).mp (hle hw)).2 t i j⟩
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rp_comm {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (κ : Module.End ℂ M) (g : X → X) :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, κ * b i y = b i (g y) * κ) →
      ∀ x : Fin n → X, κ * rp n b x = rp n b (fun i => g (x i)) * κ := by
  intro n
  induction n with
  | zero => intro b _ x; rw [rp_zero, rp_zero, mul_one, one_mul]
  | succ n ih =>
    intro b hb x
    have h := ih (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    rw [rp_succ, rp_succ, ← mul_assoc, h, mul_assoc, hb, ← mul_assoc]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telGrp :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (κ : Module.End ℂ M) (g : X → X),
      (∀ i y, κ * a i y = a i (g y) * κ) → (∀ i y, κ * b i y = b i (g y) * κ) →
      ∀ f f' : X →ₗ[ℂ] M, (∀ y, κ (f y) = f' (g y)) → ∀ x : Fin n → X, κ (tel n a b f x) = tel n a b f' fun i => g (x i) := by
  intro X M _ _ _ _ n
  induction n with
  | zero => intro a b κ g _ _ f f' _ x; rw [tel_zero, tel_zero, map_zero]
  | succ n ih =>
    intro a b κ g ha hb f f' hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) κ g (fun i y => ha i.succ y) (fun i y => hb i.succ y) f f' hf (Fin.tail x)
    have h2 := LinearMap.congr_fun (rp_comm κ g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)) (f (x 0))
    have h3 := LinearMap.congr_fun (ha 0 (x 0)) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x))
    simp only [Module.End.mul_apply] at h2 h3
    rw [tel_succ, tel_succ, map_add (f := _), h2, h3, h1, hf]
    rfl
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem UpperTheory.V.AlgRepEndIrreducible.telSum_commute_rp {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) : ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ j y, Commute T (b j y)) →
      ∀ x : Fin n → X, Commute T (rp n b x) := by
  intro n
  induction n with
  | zero => intro b _ x; rw [rp_zero]; exact Commute.one_right T
  | succ n ih =>
    intro b h x
    rw [rp_succ]
    exact (ih (Fin.tail b) (fun j y => h j.succ y) (Fin.tail x)).mul_right (h 0 (x 0))

theorem UpperTheory.V.AlgRepEndIrreducible.telSum :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M),
      (∀ i j x y, Commute (a i x) (b j y)) → ∀ (m : M) (f : X →ₗ[ℂ] M), (∀ i y, f y = a i y m - b i y m) →
      ∀ x : Fin n → X, tel n a b f x = (List.ofFn fun i => a i (x i)).prod m - rp n b x m := by
  intro X M _ _ _ _ n
  induction n with
  | zero =>
    intro a b _ m f _ x
    rw [tel_zero, rp_zero]
    simp
  | succ n ih =>
    intro a b hc m f hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) (fun i j u v => hc i.succ j.succ u v) m f (fun i y => hf i.succ y)
      (Fin.tail x)
    have h2 : Commute (a 0 (x 0)) (rp n (Fin.tail b) (Fin.tail x)) :=
      UpperTheory.V.AlgRepEndIrreducible.telSum_commute_rp _ n _ (fun j y => hc 0 j.succ (x 0) y) _
    have h3 : a 0 (x 0) (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (a 0 (x 0) m) :=
      LinearMap.congr_fun h2.eq m
    rw [tel_succ, rp_succ, h1, hf 0 (x 0), List.ofFn_succ, List.prod_cons, map_sub, map_sub, h3,
      Module.End.mul_apply, Module.End.mul_apply]
    simp only [Fin.tail]
    abel
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem qdet_intertw {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {k : ℕ}
    (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q, R ∘ₗ X p q = Y p q ∘ₗ R) (v : ℂ) :
    R ∘ₗ Formalism.REAL.qdet X v = Formalism.REAL.qdet Y v ∘ₗ R := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R}
      mul_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 ∘ₗ y.1) = (x.2 ∘ₗ y.2) ∘ₗ R
        rw [← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
      add_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 + y.1) = (x.2 + y.2) ∘ₗ R
        rw [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
      algebraMap_mem' := fun c => by
        change R ∘ₗ (algebraMap ℂ (Module.End ℂ M) c) = (algebraMap ℂ (Module.End ℂ M') c) ∘ₗ R
        ext φ; simp }
  let Z : Fin k → Fin k → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = Formalism.REAL.qdet X v :=
    map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = Formalism.REAL.qdet Y v :=
    map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.AlgRepEndIrreducible.tensA :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), tensorK π Ξ k * lieA π Ξ (toL X) = lieA π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ u : ℂ,
        Formalism.REAL.qdet (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ) (u + ((a : ℂ) - 1) / 2) =
          (m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  intro E _ _ _ a π Ξ
  let f : Module.End ℂ π.V →ₐ[ℂ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hf : ∀ X, lieA π Ξ X = f (lieOp π X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hf, hf, hf, ← map_mul f, ← map_mul f, ← map_sub f]
    congr 1
    exact LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((lie_comm (toL X) (toL Y)).trans
      (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm) φ.1)
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : π.op (.cpt k) (lieOp π (toL X) φ) = lieOp π (toL (k.1 * X * star k.1)) (π.op (.cpt k) φ) :=
      Subtype.ext (LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ.1)
    simp only [mul_apply_eq_comp, tensorK, lieA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · have e : eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ =
        fun i j => f (eL (N := Module.End ℂ π.V) (lieOp π) τ i j) := by
      funext i j
      simp only [eL, hf, map_smul, map_sub]
    have h := qdet_intertw π.V.subtype (eL (N := Module.End ℂ π.V) (lieOp π) τ) (Eop τ) (fun _ _ => rfl)
      (u + ((a : ℂ) - 1) / 2)
    have h2 : Formalism.REAL.qdet (eL (N := Module.End ℂ π.V) (lieOp π) τ) (u + ((a : ℂ) - 1) / 2) =
        (m.map (u + ·)).prod • (1 : Module.End ℂ π.V) :=
      LinearMap.ext fun φ => Subtype.ext ((LinearMap.congr_fun h φ).trans (hm.2 u φ.1 φ.2))
    rw [e, ← map_qdet, h2, map_smul, map_one]
end
