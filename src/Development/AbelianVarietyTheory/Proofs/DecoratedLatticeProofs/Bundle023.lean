module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecAuxiliaryBasisVectorSumFinApply
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymChain.LatClass
open GlobalTheory.SymChain GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_lt_one_of_unif {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) < 1 :=
  (h _).2 le_rfl


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem irreducible_of_unif {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) :
    Irreducible (⟨(ϖ : k), (valuation_lt_one_of_unif h).le⟩ : 𝒪[k]) := by
  have h1 := valuation_lt_one_of_unif h
  refine ⟨Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1, fun a b hab => ?_⟩
  by_contra hn
  rw [not_or] at hn
  have ha : valuation k (a : k) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.1
  have hb : valuation k (b : k) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.2
  have e : (ϖ : k) = (a : k) * b := congrArg Subtype.val hab
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  have : valuation k (ϖ : k) < valuation k (ϖ : k) := by
    calc valuation k (ϖ : k) = valuation k (a : k) * valuation k (b : k) := by rw [e, map_mul]
      _ ≤ valuation k (ϖ : k) * valuation k (b : k) := mul_le_mul_left ((h _).1 ha) _
      _ < valuation k (ϖ : k) * 1 := mul_lt_mul_of_pos_left hb h0
      _ = _ := mul_one _
  exact lt_irrefl _ this

section
variable {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem chainLat_eq_latOf (ϖ : kˣ) (p : 𝒪[k]) (hp : (p : k) = ϖ) (o : ι ≃ n ⊕ Fin c) :
    chainLat p c (stdLat k n) = latOf (typeFrame ϖ o).bas := by
  ext y
  rw [mem_chainLat, mem_latOf_typeFrame, mem_stdLat, hp]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  have h0 : ((ϖ : k) ^ (i.val + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hv : 0 < valuation k ((ϖ : k) ^ (i.val + 1)) := by simp [zero_lt_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [ha, map_mul]
    exact mul_le_of_le_one_left' a.2
  · intro h
    refine ⟨⟨y (.inr i) / (ϖ : k) ^ (i.val + 1), ?_⟩, by simp [div_mul_cancel₀ _ h0]⟩
    rw [Valuation.mem_integer_iff, map_div₀]
    exact (div_le_one₀ hv).2 h

end

section
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_latOf (u g : GL Y k) : act u (latOf g) = latOf (u * g) := by
  ext v
  rw [mem_act_iff_inv, ← mulVec_mem_latOf u, mulVec_mulVec, Units.mul_inv, one_mulVec]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mapsInto_latOf_iff (g : GL Y k) (g' : GL Y' k) (x : Matrix Y Y' k) :
    MapsInto x (latOf g') (latOf g) ↔ IntM ((g⁻¹).val * x * g'.val) := by
  constructor
  · intro h i j
    have h1 : g'.val *ᵥ Pi.single j 1 ∈ latOf g' := by
      have := (mulVec_mem_latOf g' (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := h _ h1 i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
  · intro h y hy i
    have : (g⁻¹).val *ᵥ (x *ᵥ y) = ((g⁻¹).val * x * g'.val) *ᵥ ((g'⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (h i l) (hy l)

end

theorem oneClass_symChain (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (s κ : ℕ) (S : SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] : S.OneClass t ν := by
  intro j c H h hf
  have h1 := valuation_lt_one_of_unif S.unif
  let p : 𝒪[k] := ⟨(S.ϖ : k), h1.le⟩
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have e := chainLat_eq_latOf S.ϖ p rfl o
  have e' := chainLat_eq_latOf S.ϖ p rfl o'
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  obtain ⟨r, hr, u, hu, hh⟩ := (oneCoset (n := XIx (Fin κ) t (j + 1)) (c := c + 1) (by omega)
    (irreducible_of_unif S.unif) S.cond hν (stdLat k (XIx (Fin κ) t j))).1 (S.μ (j + 1))
    ((S.T t).Phi j (c + 1) (by omega)) ((Chain.ofType_regular _ _ _ _ _).1 j (c + 1) _) (by
      intro x hx
      change MapsInto x (chainLat p _ _) (chainLat p _ _)
      rw [e, e', mapsInto_latOf_iff]
      rw [hΦ] at hx
      intro a b
      simpa [LatFrame.coords, typeFrame] using
        TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm a)) (o'.symm b)) (by
      intro x y hy
      change MapsInto y (chainLat p _ _) (chainLat p _ _) at hy
      rw [e, e', mapsInto_latOf_iff] at hy
      rw [hΦ, hΦ]
      have : ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') (x + (S.ϖ : k) • y)).submatrix (ixSucc _ t j) id =
          ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id +
          (S.ϖ : k) • ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') y).submatrix (ixSucc _ t j) id := by
        simp only [LatFrame.coords, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        rfl
      refine (congrArg _ this).trans (TypeDatum.Phi_add _ (S.tame _) _ fun a b => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (hy _ _)) 1 h (act_one _) hf
  refine ⟨r, hr, u, mem_stabLat_iff.2 ?_, hh⟩
  change act u (chainLat p _ _) = chainLat p _ _ at hu
  rw [e, act_latOf] at hu
  exact hu

end GlobalTheory.SymChain.LatClass
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.TopCongr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_invariant {a b : Type} [Fintype a] [DecidableEq a] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix a a k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (g * x) = f x := by
  by_cases hx : IntM x
  · have e : g * x = x + (g - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
    rw [e, hp x _ hx (hg.mul_intM hx)]
  · obtain ⟨u, hu, rfl⟩ := exists_mem_KOne hg
    have h1 : f x = 0 := by_contra fun h => hx (hs x h)
    have h2 : f (u.val * x) = 0 := by_contra fun h => hx (by
      have := (mem_KO.1 (KOne_le_KO hu)).2.mul (hs _ h)
      rwa [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this)
    rw [h1, h2]

theorem hat_eq_zero [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem phiTop_eq (z : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) (XIx (Fin κ) t (s + 1) ⊕ Fin 0) k) :
    (S.T t).PhiTop z = (S.P.iter t S.μ S.tame (s + 1)).Phi t (S.μ (s + 1 + 1))
      (z.submatrix (ixSucc _ t (s + 1)) (stdOrd (Fin κ) t (s + 1) 0 rfl)) := by
  have e : (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (s + 1) 0 rfl)).bas = 1 := by
    change embA _ _ = 1
    rw [Subsingleton.elim (SplitFlip.diagGL _) 1, map_one]
  change S.P.iterPhi t S.μ S.tame (s + 1) (LatFrame.coords _ _ z) = _
  unfold LatFrame.coords TypeDatum.iterPhi
  rw [e]
  simp [LatFrame.refl, typeFrame]

theorem symmetricChain_psi_base_eq_one_of_maximalIdeal {d : XIx (Fin κ) t (s + 1) → k} (hd : ∀ i, valuation k (d i) < 1) :
    S.ψ (-1 * (d ⬝ᵥ S.y0 t)) = 1 := by
  refine (S.cond 1).2 (by simp) _ ?_
  have h := (S.unif _).1 (hd (Sum.inl (Sum.inr 0)))
  have h0 : (0 : ValueGroupWithZero k) < valuation k (S.ϖ : k) := by
    rw [zero_lt_iff]; simp
  simp only [SymData.y0, dotProduct_single, neg_mul, one_mul, Valuation.map_neg, map_mul, map_one,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [← div_eq_mul_inv]
  exact (div_le_one₀ h0).2 h

theorem xiTop_mul_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (g : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) k), (∀ r c, valuation k ((g - 1) r c) < 1) → ∀ x : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k, (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (g * x) = (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ g hg x
  refine mul_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x
  · unfold Chain.xiTop at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rintro (i | i) j
    · rw [phiTop_eq] at h1
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i)
        ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))
    · exact by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))
  · unfold Chain.xiTop
    have hxy := hx.add hy.intM
    rw [Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _),
      phiTop_eq, phiTop_eq]
    congr 1
    · have e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0 := by
        ext i (j | j)
        · rfl
        · exact j.elim0
      rw [e, submatrix_add]
      refine TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_
      rw [submatrix_apply]
      rcases stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j
      · exact hy _ _
      · exact j.elim0
    · have e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ()) := rfl
      rw [e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]

end GlobalTheory.TopCongr
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section Field
variable {F : Type} [Field F] {κ l : ℕ}

theorem mul_fromBlocks_inl (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin κ) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inl j) = ∑ t, M a (Sum.inl t) * C t j := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem mul_fromBlocks_inr (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin l) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inr j) = M a (Sum.inr j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem pat_of_mul (ρ : ℕ) (u : GL (Fin κ ⊕ Fin l) F) (hu : InN (ρ + 1) u) (γ : GL (Fin κ) F)
    (hγ : IsUpperUnip Fin.val γ.val) :
    ∀ a b, ¬ FreeTop ρ a b → (u * embX l γ).val a b = (1 : Matrix _ _ F) a b := by
  intro a b hab
  have hv : (u * embX l γ).val = u.val * fromBlocks γ.val 0 0 1 := by
    rw [Units.val_mul, Radical.embX_val]
  rw [hv]
  rcases a with i | i <;> rcases b with j | j <;> simp only [FreeTop, not_lt] at hab
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inl i) (Sum.inl t) = if i = t then 1 else 0 := fun t => by
      rw [hu (Sum.inl i) (Sum.inl t) le_rfl, Matrix.one_apply]; simp
    simp only [hu', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hγ i j (by exact_mod_cast hab)]
    simp [Matrix.one_apply]
  · rw [mul_fromBlocks_inr, hu (Sum.inl i) (Sum.inr j) (Nat.succ_le_succ hab)]
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
      rw [hu (Sum.inr i) (Sum.inl t) (Nat.succ_le_succ hab)]; simp
    simp [hu']
  · rw [mul_fromBlocks_inr, hu (Sum.inr i) (Sum.inr j) (Nat.succ_le_succ hab)]

theorem exists_of_pat (ρ : ℕ) (gb : GL (Fin κ ⊕ Fin l) F)
    (h : ∀ a b, ¬ FreeTop ρ a b → gb.val a b = (1 : Matrix _ _ F) a b) :
    ∃ u : GL (Fin κ ⊕ Fin l) F, InN (ρ + 1) u ∧ ∃ γ : GL (Fin κ) F,
      IsUpperUnip Fin.val γ.val ∧ gb = u * embX l γ := by
  have hU : IsUpperUnip Fin.val gb.val.toBlocks₁₁ := fun r t hrt => by
    have := h (Sum.inl r) (Sum.inl t) (by simp only [FreeTop, not_lt]; exact hrt)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have hdet : gb.val.toBlocks₁₁.det = 1 := Radical.Uni.det (b := Fin.val) hU
  let γ : GL (Fin κ) F := ⟨gb.val.toBlocks₁₁, gb.val.toBlocks₁₁⁻¹,
    Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one),
    Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)⟩
  refine ⟨gb * (embX l γ)⁻¹, ?_, γ, hU, (inv_mul_cancel_right gb _).symm⟩
  have hv : (gb * (embX l γ)⁻¹).val = gb.val * fromBlocks (γ⁻¹).val 0 0 1 := by
    rw [Units.val_mul, ← map_inv, Radical.embX_val]
  intro r t hrt
  rw [hv]
  rcases r with i | i <;> rcases t with j | j
  · rw [mul_fromBlocks_inl]
    have hm : ∑ q, gb.val (Sum.inl i) (Sum.inl q) * (γ⁻¹).val q j =
        (1 : Matrix (Fin κ) (Fin κ) F) i j := by
      have := congrFun (congrFun γ.mul_inv i) j
      rw [Matrix.mul_apply] at this
      exact this
    rw [hm]
    simp [Matrix.one_apply]
  · have hrt' : j.val + 1 ≤ ρ + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; omega)
  · have hrt' : ρ + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inl]
    have hz : ∀ q, gb.val (Sum.inr i) (Sum.inl q) = 0 := fun q => by
      have := h (Sum.inr i) (Sum.inl q) (by simp only [FreeTop, not_lt]; omega)
      simpa [Matrix.one_apply] using this
    simp [hz]
  · have hrt' : j.val + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; exact Fin.le_def.mpr (by omega))

end Field

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem valuation_lt_one_iff_residue_eq_zero (y : 𝒪[k]) :
    valuation k (y : k) < 1 ↔ IsLocalRing.residue 𝒪[k] y = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.symm

theorem entry_lt_iff (g₀ : GL ι 𝒪[k]) (a b : ι) :
    valuation k ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b) < 1 ↔
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b = (1 : Matrix ι ι 𝓀[k]) a b := by
  have e1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b =
      ((g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b : 𝒪[k]) : k) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab] <;> rfl
  have e2 : (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b -
      (1 : Matrix ι ι 𝓀[k]) a b = IsLocalRing.residue 𝒪[k] (g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e1, valuation_lt_one_iff_residue_eq_zero, ← e2, sub_eq_zero]

end Local

end GlobalTheory.SymPattern

theorem GlobalTheory.SymChain.SymData.mem_J_iff_pattern :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k),
      g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  intro k _ _ _ _ s κ S g
  rw [S.sym.1 g]
  constructor
  · rintro ⟨u, hu, γ, hγ, g₀, hg₀, hgb⟩
    refine ⟨⟨g₀, hg₀⟩, fun a b hab => ?_⟩
    rw [← hg₀, SymPattern.entry_lt_iff, hgb]
    exact SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
  · rintro ⟨⟨g₀, hg₀⟩, hpat⟩
    obtain ⟨u, hu, γ, hγ, he⟩ := SymPattern.exists_of_pat S.ρ
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀) (fun a b hab => by
        rw [← SymPattern.entry_lt_iff, hg₀]; exact hpat a b hab)
    exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, g₀, hg₀, he⟩
end
end
