module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle164
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
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

theorem act_sum_blocks (Z : Mat P Q) (A E : Matrix (Fin P) (Fin Q) ℂ) (x d : Ix P Q → ℂ) (t : ℂ) :
    (∑ i, ∑ k, Z (.inl k) (.inl i) * (x (.inl i) * d (.inl k) + ∑ j, A i j * E k j + if i = k then t / 2 else 0) -
      ∑ i, ∑ j, Z (.inr j) (.inl i) * (x (.inl i) * (x (.inr j) * t + ∑ m, A m j * d (.inl m)) +
        (∑ k, A i k * (x (.inr j) * d (.inr k) + ∑ m, A m j * E m k) + A i j * t))) +
    (∑ j, ∑ i, Z (.inl i) (.inr j) * E i j -
      ∑ j, ∑ k, Z (.inr k) (.inr j) * (x (.inr k) * d (.inr j) + ∑ i, A i k * E i j + if j = k then t / 2 else 0)) =
    (Z.trace / 2 + dS Z A x) * t + (∑ i, ∑ j, dA Z A i j * E i j + ∑ l, dX Z A x l * d l) := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
    have h11 : (0 : Mat P Q).toBlocks₁₁ = 0 := rfl
    have h12 : (0 : Mat P Q).toBlocks₁₂ = 0 := rfl
    have h21 : (0 : Mat P Q).toBlocks₂₁ = 0 := rfl
    have h22 : (0 : Mat P Q).toBlocks₂₂ = 0 := rfl
    simp [dS, dA, dX, h11, h12, h21, h22]
  | h_add Z W hZ hW =>
    have h11 : (Z + W).toBlocks₁₁ = Z.toBlocks₁₁ + W.toBlocks₁₁ := rfl
    have h12 : (Z + W).toBlocks₁₂ = Z.toBlocks₁₂ + W.toBlocks₁₂ := rfl
    have h21 : (Z + W).toBlocks₂₁ = Z.toBlocks₂₁ + W.toBlocks₂₁ := rfl
    have h22 : (Z + W).toBlocks₂₂ = Z.toBlocks₂₂ + W.toBlocks₂₂ := rfl
    have hS : dS (Z + W) A x = dS Z A x + dS W A x := by
      simp only [dS, h21, h22, Matrix.add_mul, Matrix.trace_add, Matrix.add_mulVec, dotProduct_add]; ring
    have hA : dA (Z + W) A = dA Z A + dA W A := by
      simp only [dA, h11, h12, h21, h22, Matrix.add_mul, Matrix.mul_add]; abel
    have hX : dX (Z + W) A x = dX Z A x + dX W A x := by
      simp only [dX, h11, h21, h22, Matrix.add_mul, Matrix.mul_add, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.vecMul_add]
      ext (i | j) <;> simp <;> ring
    simp only [hS, hA, hX, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, Matrix.trace_add]
    simp only [add_mul] at hZ hW
    linear_combination hZ + hW
  | h_std_basis a b c =>
    rcases a with a | a <;> rcases b with b | b <;>
    simp [dS, dA, dX, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.single_apply, Matrix.mul_apply, Matrix.trace, Matrix.mulVec, Matrix.vecMul, dotProduct, ite_and,
      Fintype.sum_sum_type]
    · simp only [mul_add, Finset.mul_sum, mul_assoc]
      split_ifs <;> ring
    · rw [Finset.sum_comm (f := fun i k => A i a * (c * A b k) * E i k)]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, mul_left_comm]
      ring
    · simp only [mul_add, Finset.mul_sum, mul_assoc, mul_left_comm]
      split_ifs <;> ring


open MvPolynomial GlobalTheory.Oscillator in
theorem inner_omAct0_adjZ : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  intro P Q F A x v h1 h2 Z f
  have hh : ∀ (p : Prop) [Decidable p], inner ℂ (F.ι (if p then (1 / 2 : ℂ) • f else 0)) v =
      if p then inner ℂ (F.ι f) v / 2 else 0 := by
    intro p _
    split_ifs
    · rw [map_smul, inner_smul_left]; simp [map_ofNat]; ring
    · simp
  have hd : ∀ k j : Fin Q, inner ℂ (F.ι (pderiv (Sum.inr k) (X (Sum.inr j) * f))) v =
      x (.inr j) * inner ℂ (F.ι (pderiv (.inr k) f)) v +
        ∑ m, A m j * inner ℂ (F.ι (pderiv (.inl m) (pderiv (.inr k) f))) v +
        if k = j then inner ℂ (F.ι f) v else 0 := by
    intro k j
    rw [← h2, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), inner_add_left, pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← act_sum_blocks Z A (fun i j => inner ℂ (F.ι (pderiv (Sum.inl i) (pderiv (Sum.inr j) f))) v) x
    (fun l => inner ℂ (F.ι (pderiv l f)) v) (inner ℂ (F.ι f) v), omAct0_eq, oscAct_apply]

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner, inner_smul_left,
  adjZ_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, LinearMap.add_apply, map_add, inner_add_left]
  simp only [unitOp_inl_inl, unitOp_inl_inr, unitOp_inr_inl, unitOp_inr_inr, map_add (f := _), map_sub, map_neg,
    inner_add_left, inner_sub_left, inner_neg_left, hh, h1, h2, hd, sgn, map_mul, Complex.conj_conj,
    Int.cast_one, Int.cast_neg, map_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hc : ∀ (j : Fin Q) (i : Fin P), pderiv (Sum.inr j) (pderiv (Sum.inl i) f) =
      pderiv (Sum.inl i) (pderiv (Sum.inr j) f) := fun j i => pderiv_pderiv_comm _ _ _
  rw [add_add_add_comm]
  simp only [hc, mul_add (A _ _), Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 2 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_ <;> ring

end GlobalTheory.OscGauss
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaStab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem tr_one (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp [GStep.tr, trFr_apply, frMul_one]

theorem evV_rho (b : S.β) (g : S.G b) (v : VV K lam) :
    _root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (_root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine _root_.Formalism.L2.Col.evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem tr_mem (b : S.β) (g : S.G b)
    {F : Fr emb σ n → ℂ} (hF : F ∈ ValC (Gr emb σ n) lam) : S.tr emb σ b g F ∈ ValC (Gr emb σ n) lam := by
  rw [← _root_.Formalism.L2.Col.span_evV emb 1 lam σ] at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [← evV_rho]
    exact _root_.Formalism.L2.Col.evV_mem_ValC emb 1 lam σ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_Fi (hf : S.Free)
    (φ : S.Cl → Fr emb σ n → ℂ) (h : ∀ c, φ c ∈ ValC (Gr emb σ n) lam) : φ ∈ S.Fi emb σ lam := fun c =>
  ⟨h c, fun g => by rw [hf c.1 g.1 _ g.2, tr_one]⟩

end General

theorem lawDiaStable : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (_hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ h
  rintro P a _ ⟨φ, hφ, rfl⟩
  exact mem_Fi _ emb σ _ h.free0 _ fun c => tr_mem _ emb σ _ _ _ (hφ _).1

end GlobalTheory.Mem.Col2.DiaStab
end
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms

section General

variable {K : Type} [Field K] (σ : K →+* ℂ) {V W C J : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]

theorem li_pi_of_basis [Finite C] [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W)
    (he : LinearIndependent ℂ fun j => ev (e j)) {κ : Type} (b : κ → C → V) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun i => fun c => ev (b i c) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let r : (C → V) →ₗ[K] (C × J → K) :=
    LinearMap.pi fun p => (e.coord p.2) ∘ₗ LinearMap.proj p.1
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    funext c
    apply e.ext_elem
    intro j
    simpa [r] using congrFun hf (c, j)
  have h1 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (hb.map' r hr)
  let T : (C × J → ℂ) →ₗ[ℂ] (C → W) :=
    LinearMap.pi fun c => ∑ j, (LinearMap.proj (c, j) : (C × J → ℂ) →ₗ[ℂ] ℂ).smulRight (ev (e j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    funext p
    have h2 : ∑ j, u (p.1, j) • ev (e j) = 0 := by
      simpa [T, LinearMap.sum_apply] using congrFun hu p.1
    exact Fintype.linearIndependent_iff.1 he (fun j => u (p.1, j)) h2 p.2
  have h3 := h1.map' T hT
  suffices hs : (fun i => fun c => ev (b i c)) = T ∘ fun i => algebraMap K ℂ ∘ (r ∘ b) i by
    rw [hs]
    exact h3
  funext i c
  have h4 : b i c = ∑ j, e.repr (b i c) j • e j := (e.sum_repr _).symm
  conv_lhs => rw [h4]

  simp only [map_sum, LinearMap.map_smulₛₗ]
  simp [T, r, LinearMap.sum_apply, RingHom.algebraMap_toAlgebra]

theorem mem_span_basis_image [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W) (x : V) :
    ev x ∈ Submodule.span ℂ (Set.range fun j => ev (e j)) := by

  rw [← e.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem rho_sum_translates {G : Type} [Group G] [Fintype G] (ρ : G →* Module.End K V) (g : G) (x : V) :
    ρ g (∑ t, ρ t x) = ∑ t, ρ t x := by

  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun t => ?_
  simp [map_mul]

end General

namespace GStep

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)


omit [StarRing E] [StarRing K] in
theorem evV_rho_eq_tr (b : S.β) (g : S.G b) (F : VV K lam) :
    _root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g F) =
      S.tr emb σ b g (_root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) := by
  funext y
  have h1 : S.rho emb lam b g F = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) F := rfl
  rw [h1, LinearMap.map_smulₛₗ, tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine _root_.Formalism.L2.Col.evV_rhoVr_tr emb _ lam σ _ F y _ ?_
  have h2 : y = frMul emb σ (S.gam b g) (frMul emb σ (S.gam b g)⁻¹ y) := by
    rw [← frMul_mul, mul_inv_cancel, frMul_one]
  intro τ
  exact congrFun (congrArg Subtype.val h2) τ

theorem lawBasis_of_ok (h : (S.fam emb lam).Ok) : S.LawBasis emb σ lam h := by
  classical
  haveI : Fintype S.Cl := h.fintypeCl
  constructor
  · have h1 : LinearIndependent K fun a => ((S.csd emb lam h).basis a).1 :=
      (S.csd emb lam h).basis.linearIndependent.map' (S.csd emb lam h).Forms.subtype (Submodule.ker_subtype _)
    exact li_pi_of_basis σ (C := S.Cl) (S.csd emb lam h).bV (_root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ)
      (_root_.Formalism.L2.Col.evV_linearIndependent emb _ lam σ (fr0 emb σ n) _ (S.csd emb lam h).bV.linearIndependent) _ h1
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩ c
      refine ⟨_root_.Formalism.L2.Col.evV_mem_ValC emb _ lam σ _, fun g => ?_⟩
      have h1 := ((S.csd emb lam h).basis a).2 c g
      have h2 := S.evV_rho_eq_tr emb σ lam c.1 g.1 (((S.csd emb lam h).basis a).1 c)
      exact h2.symm.trans (congrArg (_root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) h1)
    · intro φ hφ
      rw [← Finset.univ_sum_single φ]
      refine Submodule.sum_mem _ fun c _ => ?_
      letI : Fintype (S.Stab c) := (S.csd emb lam h).finGam c
      let A : (Fr emb σ n → ℂ) →ₗ[ℂ] (S.Cl → Fr emb σ n → ℂ) :=
        LinearMap.single ℂ (fun _ : S.Cl => Fr emb σ n → ℂ) c ∘ₗ ∑ g : S.Stab c, (S.tr emb σ c.1 g.1).toLinearMap
      have hA : ∀ w, A w = Pi.single c (∑ g : S.Stab c, S.tr emb σ c.1 g.1 w) := fun w => by
        simp [A, LinearMap.sum_apply]
      have hle : ValC (Gr emb σ n) lam ≤ (Submodule.span ℂ
          (Set.range fun a => S.embF emb σ lam h ((S.hlat emb lam h).b a))).comap A := by
        rw [← _root_.Formalism.L2.Col.span_evV, Submodule.span_le]
        rintro _ ⟨F, rfl⟩
        let ρc : S.Stab c →* Module.End K (VV K lam) :=
          (S.rho emb lam c.1).comp (MulAction.stabilizer (S.G c.1) (S.rep c)).subtype
        let x : S.FormsK emb lam h := ⟨(Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam), by
          intro c' γ
          by_cases hc : c' = c
          · subst hc
            show ρc γ ((Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_same]
            exact rho_sum_translates ρc γ F
          · show S.rho emb lam c'.1 γ.1 ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_of_ne hc, map_zero]⟩
        have hx : A (_root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) = S.embF emb σ lam h x := by
          rw [hA]
          funext c'
          show _ = _root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c')
          by_cases hc : c' = c
          · subst hc

            rw [Pi.single_eq_same, Pi.single_eq_same, map_sum]
            exact Finset.sum_congr rfl fun g _ => (S.evV_rho_eq_tr emb σ lam c'.1 g.1 F).symm
          · rw [Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc, map_zero]
        rw [SetLike.mem_coe, Submodule.mem_comap, hx]
        exact mem_span_basis_image σ (S.hlat emb lam h).b (S.embF emb σ lam h) x
      have h1 := Submodule.mem_comap.1 (hle (hφ c).1)
      have h2 : A (φ c) = (Fintype.card (S.Stab c) : ℂ) • (Pi.single c (φ c) : S.Cl → Fr emb σ n → ℂ) := by
        rw [hA, Finset.sum_congr rfl fun g _ => (hφ c).2 g, Finset.sum_const, Finset.card_univ, ← Pi.single_smul',
          Nat.cast_smul_eq_nsmul]
      rw [h2] at h1
      exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1

end GStep

theorem lawBasis_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h :=
  fun S emb σ lam _ _ h => S.lawBasis_of_ok emb σ lam h

end GlobalTheory.Mem.Col2
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

open Formalism.HermitianLatticesTheory (localization₂)

namespace GlobalTheory.Mem.CosetFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


omit [StarRing E] in
theorem exists_reps (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x - t = (m : 𝓞 E) • z := by
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  let M : Submodule ℤ N := LinearMap.range (LinearMap.lsmul ℤ N (m : ℤ))
  haveI : Finite (N ⧸ M) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
    show (m : ℤ) • (Submodule.Quotient.mk y : N ⧸ M) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨Set.range fun q : N ⧸ M => ((Quotient.out q : N) : Sp E n), Set.finite_range _, fun x hx => ?_⟩
  refine ⟨_, ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩, ?_⟩
  have h : (⟨x, hx⟩ : N) - Quotient.out (Submodule.Quotient.mk (p := M) ⟨x, hx⟩) ∈ M :=
    (Submodule.Quotient.eq M).1 (Quotient.out_eq _).symm
  obtain ⟨z, hz⟩ := h
  refine ⟨z, z.2, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [LinearMap.lsmul_apply, AddSubgroupClass.coe_sub, natCast_zsmul] at h2
  rw [← h2, Nat.cast_smul_eq_nsmul]
  rfl

theorem exists_reps_loc (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧
      ∀ x ∈ localization₂ P.asIdeal N, ∃ t ∈ T, ((m : E)⁻¹) • (x - t) ∈ localization₂ P.asIdeal N := by
  obtain ⟨T, hT, h⟩ := exists_reps N hN m hm
  refine ⟨T, hT, fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := (mem_locP P N x).1 hx
  have hk : ∀ k : ℕ, s ^ (k + 1) • x ∈ N := fun k => by
    rw [pow_succ, mul_smul]; exact N.smul_mem _ hsx
  choose t ht z hz he using fun k => h _ (hk k)
  haveI := hT.to_subtype
  obtain ⟨i, j, hij, hEq⟩ : ∃ i j : ℕ, i < j ∧ t i = t j := by
    obtain ⟨a, b, hab, h1⟩ := Finite.exists_ne_map_eq_of_infinite (fun k => (⟨t k, ht k⟩ : T))
    have h1' : t a = t b := congrArg Subtype.val h1
    rcases lt_or_gt_of_ne hab with h2 | h2
    · exact ⟨a, b, h2, h1'⟩
    · exact ⟨b, a, h2, h1'.symm⟩
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨t p, ht p, (mem_locP P N _).2 ⟨s ^ (i + 1), fun hh => hs (P.isPrime.mem_of_pow_mem _ hh), ?_⟩⟩
  have hm' : (m : E) ≠ 0 := by exact_mod_cast hm
  have e1 : s ^ (i + 1) • (x - t p) = (m : 𝓞 E) • (z i - z (i + p + 1) + s ^ (i + 1) • z p) := by
    rw [smul_add, smul_sub (m : 𝓞 E), ← he i, ← he (i + p + 1), smul_comm (m : 𝓞 E), ← he p, hEq, smul_sub, smul_sub,
      ← mul_smul, ← pow_add, show i + 1 + (p + 1) = i + p + 1 + 1 by ring]
    abel
  rw [smul_comm, e1, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hm']
  exact N.add_mem (N.sub_mem (hz _) (hz _)) (N.smul_mem _ (hz _))

theorem exists_reps_pow (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : ℤ) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x : Sp E n, ((qOf P : E) ^ a)⁻¹ • x ∈ localization₂ P.asIdeal N →
      ∃ t ∈ T, ((qOf P : E) ^ b)⁻¹ • (x - t) ∈ localization₂ P.asIdeal N := by
  have hq : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hq' : (qOf P : E) ≠ 0 := by exact_mod_cast hq
  obtain ⟨T, hT, h⟩ := exists_reps_loc P N hN (qOf P ^ (b - a).toNat) (pow_ne_zero _ hq)
  refine ⟨(fun t => (qOf P : E) ^ a • t) '' T, hT.image _, fun x hx => ?_⟩
  obtain ⟨t, ht, h1⟩ := h _ hx
  refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
  have h2 := (localization₂ P.asIdeal N).smul_mem ((qOf P ^ (a - b).toNat : ℕ) : 𝓞 E) h1
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h2
  have e : ((qOf P ^ (a - b).toNat : ℕ) : E) * ((qOf P ^ (b - a).toNat : ℕ) : E)⁻¹ = ((qOf P : E) ^ b)⁻¹ * (qOf P : E) ^ a := by
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ hq', ← zpow_add₀ hq']
    congr 1
    omega
  rw [smul_smul, e, mul_smul, smul_sub, smul_inv_smul₀ (zpow_ne_zero _ hq')] at h2
  exact h2

theorem finite_cosets (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : SB → ℤ) :
    {Y : Set (Sp E n) | ∃ y ∈ locLat SB N a, Y = {z | z - y ∈ locLat SB N b}}.Finite := by
  choose T hT h using fun P : SB => exists_reps_pow P.1 N hN (a P) (b P)
  refine ((Set.Finite.pi' hT).image fun t : SB → Sp E n =>
    {z | ∀ P : SB, ((qOf P.1 : E) ^ b P)⁻¹ • (z - t P) ∈ localization₂ P.1.asIdeal N}).subset ?_
  rintro Y ⟨y, hy, rfl⟩
  choose t ht h1 using fun P => h P y ((mem_locLat SB N a y).1 hy P)
  refine ⟨t, ht, ?_⟩
  ext z
  simp only [Set.mem_setOf_eq, mem_locLat]
  refine forall_congr' fun P => ?_
  have e : z - t P = (z - y) + (y - t P) := by abel
  rw [e, smul_add]
  exact (localization₂ P.1.asIdeal N).add_mem_iff_left (h1 P)

theorem ysAt_finite_nonempty : ∀ {X : Fields} {Pr : Primes X} (R : Ranks)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))), Submodule.IsLattice X.E N →
      ((ysAt R sel mu cst j).ys N).Finite ∧ ((ysAt R sel mu cst j).ys N).Nonempty := by
  intro X Pr R sel S mu cst j N hN
  unfold ysAt
  split_ifs
  · exact ⟨finite_cosets _ N hN.fg _ _, _, 0, zero_mem _, rfl⟩
  · exact ⟨Set.finite_singleton _, Set.singleton_nonempty _⟩

end GlobalTheory.Mem.CosetFin
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  first | exact @GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow | exact GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow | (intros; apply GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryScalar_eq_one_mod_of_fixes_simple_module : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : Module.finrank F E = 2) (_ : ∀ x, σ (σ x) = x) (_ : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (_ : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (_ : T.Prime)
    (_ : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (M : Type) [AddCommGroup M] [Module (intV E v) M] (_ : Nat.card M = T) (m : M) (_ : m ≠ 0) (d c : intV E v) (_ : (d - 1) • m = 0)
    (_ : sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F)),
    ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := by
  first | exact @GlobalTheory.UnitaryScalarModT.eq_one_add_of_fixes | exact GlobalTheory.UnitaryScalarModT.eq_one_add_of_fixes | (intros; apply GlobalTheory.UnitaryScalarModT.eq_one_add_of_fixes <;> assumption)
end
