module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle861
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv


attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory in
open MonObj in
theorem isCombAtG_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X0 : Scheme.{0}} (t : SAB H X0) {R : Type} [CommRing R] (x : Sp R ⟶ X0) {m n : ℕ}
    (f : Fin m → Fin n) (hf : Function.Injective f)
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {v' : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ j, IsTanAtG t x (v' j)) {cf : Fin m → R} {cf' : Fin n → R}
    (hvf : ∀ k, v' (f k) = v k) (hcf : ∀ k, cf' (f k) = cf k) (hz : ∀ c, (¬ ∃ k, f k = c) → cf' c = 0)
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v cf w) : IsCombAtG t x v' cf' w := by
  classical
  have h0 : spMap (epsMul (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have e : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun z => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Spec.map_comp, e]
    rfl
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨Function.extend f u 1, fun c => ?_, ?_⟩
  · by_cases hc : ∃ k, f k = c
    · obtain ⟨k, rfl⟩ := hc
      rw [hf.extend_apply, hu, hvf, hcf]
    · let p : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
      rw [Function.extend_apply' _ _ _ hc, hz c hc, h0, Category.assoc, (hv c).2, Pi.one_apply,
        ← MonObj.comp_one p]
      rfl
  · rw [← hw]
    congr 1
    letI : CommMonoid (tEpsG x ⟶ t.G) := Hom.commMonoid
    rw [List.prod_ofFn, List.prod_ofFn]
    symm
    refine Finset.prod_of_injOn f hf.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro c _ hc
      rw [Function.extend_apply' _ _ _ ?_, Pi.one_apply]
      rintro ⟨k, rfl⟩
      exact hc ⟨k, by simp, rfl⟩
    · intro k _
      rw [hf.extend_apply]

theorem isCombAtG_flatFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ t.G.left)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (w : Sp (DualNumber S) ⟶ t.G.left), (∀ τ k, IsTanAtG t x (w' τ k)) → IsCombAtG t x (w' σ) (A σ i) w → IsCombAtG t x (fun c => w' (e'.symm c).1 (e'.symm c).2) (fun c => GlobalTheory.LogKSDiv.flatFrame A e e' (e ⟨σ, i⟩) c) w := by
  classical
  intro E _ _ _ H Dw X t S _ x n n' e e' w' A σ i w htan h
  refine isCombAtG_extend t x (fun k => e' ⟨σ, k⟩) (fun a b hab => ?_) (fun c => htan _ _) (fun k => ?_)
    (fun k => flatFrame_apply A e e' σ i k) (fun c hc => ?_) h
  · exact sigma_mk_injective (β := fun τ : E →+* ℂ => Fin (Dw.mult τ)) (e'.injective hab)
  · show (fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => w' z.1 z.2) (e'.symm (e' ⟨σ, k⟩)) = _
    rw [Equiv.symm_apply_apply]
  · obtain ⟨⟨τ, k⟩, rfl⟩ := e'.surjective c
    have hne : σ ≠ τ := by
      rintro rfl
      exact hc ⟨k, rfl⟩
    simp [flatFrame, Matrix.blockDiagonal'_apply_ne _ _ _ hne]

end GlobalTheory.LogKSDiv
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem rowWeight_le_colSum (N : ℕ) (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) d) a ≤ ∑ s, (Finsupp.weight (colW N N) d) s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  simp only [rowW, colW, Finset.sum_pi_single', Finset.mem_univ, if_true]
  apply Nat.mul_le_mul_left
  rw [Pi.single_apply]
  split_ifs <;> omega

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def wtBox (τ : ι) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (∑ s : Fin N, res N (lam τ) s + 1)

theorem sum_box (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N (res N (lam τ))) :
    ∑ w ∈ wtBox N lam τ, weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  have hc : IsWeightedHomogeneous (colW N N) f (res N (lam τ)) := by
    have := (Submodule.mem_inf.mp hf).1
    simpa [mem_weightedHomogeneousSubmodule] using this
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    have hd := hc (Ne.symm hne)
    simp only [wtBox, Fintype.mem_piFinset, Finset.mem_range]
    intro a
    have := rowWeight_le_colSum N d a
    rw [hd] at this
    omega

section Ops

variable {O N lam}

theorem isProj_idem {τ : ι} {w : Fin N → ℕ} {a : Module.End O (NablaT O N lam)} (h : IsProj O N lam τ w a) :
    a * a = a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  rw [h x y hy]
  have hy' : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ y) τ : MvPolynomial _ O) := by
    rw [Function.update_self, hy, weightedHomogeneousComponent_eq_self
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
  rw [h _ y hy', Function.update_idem]

theorem isProj_comm {τ τ' : ι} (hne : τ ≠ τ') {w w' : Fin N → ℕ} {a b : Module.End O (NablaT O N lam)}
    (ha : IsProj O N lam τ w a) (hb : IsProj O N lam τ' w' b) : a * b = b * a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  let y' : dualWeyl O N N (res N (lam τ')) := rowProj O N (res N (lam τ')) w' (x τ')
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  have hy' : (y' : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w' (x τ' : MvPolynomial _ O) := rfl
  rw [hb x y' hy', ha x y hy]
  have h1 : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ' y') τ : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne]; exact hy
  have h2 : (y' : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w' ((Function.update x τ y) τ' : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne.symm]; exact hy'
  rw [ha _ y h1, hb _ y' h2, Function.update_comm hne]

theorem isProj_sum (τ : ι) (e : (Fin N → ℕ) → Module.End O (NablaT O N lam)) (he : ∀ w, IsProj O N lam τ w (e w)) :
    ∑ w ∈ wtBox N lam τ, e w = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, Module.End.one_apply]
  have key : ∀ w, e w (PiTensorProduct.tprod O x) =
      (PiTensorProduct.tprod O).toLinearMap x τ (rowProj O N (res N (lam τ)) w (x τ)) := by
    intro w
    rw [MultilinearMap.toLinearMap_apply]
    exact he w x _ rfl
  rw [Finset.sum_congr rfl (fun w _ => key w)]

  rw [← map_sum, MultilinearMap.toLinearMap_apply]
  have : ∑ w ∈ wtBox N lam τ, rowProj O N (res N (lam τ)) w (x τ) = x τ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact sum_box O N lam τ _ (x τ).2
  rw [this, Function.update_eq_self]

end Ops

section Main

variable {O N lam}

def projA [Fintype ι] (τ : ι) (w : Fin N → ℕ) : alg O N lam :=
  ⟨(exists_unique_isProj O N ι lam τ w).choose,
    Algebra.subset_adjoin (Or.inr ⟨τ, w, (exists_unique_isProj O N ι lam τ w).choose_spec.1⟩)⟩

variable [Fintype ι]

theorem projA_isProj (τ : ι) (w : Fin N → ℕ) : IsProj O N lam τ w (projA (O := O) (lam := lam) τ w : Module.End O (NablaT O N lam)) :=
  (exists_unique_isProj O N ι lam τ w).choose_spec.1

theorem projA_eq {τ : ι} {w : Fin N → ℕ} {a : alg O N lam} (h : IsProj O N lam τ w a) : a = projA τ w :=
  Subtype.ext ((exists_unique_isProj O N ι lam τ w).choose_spec.2 _ h)

theorem projA_idem (τ : ι) (w : Fin N → ℕ) : projA (O := O) (lam := lam) τ w * projA τ w = projA τ w :=
  Subtype.ext (isProj_idem (projA_isProj τ w))

theorem projA_comm {τ τ' : ι} (hne : τ ≠ τ') (w w' : Fin N → ℕ) :
    projA (O := O) (lam := lam) τ w * projA τ' w' = projA τ' w' * projA τ w :=
  Subtype.ext (isProj_comm hne (projA_isProj τ w) (projA_isProj τ' w'))

theorem projA_sum (τ : ι) : ∑ w ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ w = 1 := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
  exact isProj_sum τ _ (projA_isProj τ)

end Main

theorem exists_jointWt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm →
    ∃ w : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w := by
  intro O _ _ _ _ N ι _ _ lam Gm _ _ _
  have step : ∀ s : Finset ι, ∃ z : Gm, z ≠ 0 ∧ ∃ w : ι → Fin N → ℕ,
      ∀ τ ∈ s, projA (O := O) (lam := lam) τ (w τ) • z = z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
      exact ⟨z, hz, 0, by simp⟩
    | insert τ s hτ ih =>
      obtain ⟨z, hz, w, hw⟩ := ih
      have hsum : ∑ v ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ v • z = z := by
        rw [← Finset.sum_smul, projA_sum, one_smul]
      obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hz)
      refine ⟨projA τ v • z, hv, Function.update w τ v, ?_⟩
      intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ
      · rw [Function.update_self, smul_smul, projA_idem]
      · have hne : σ ≠ τ := fun h => hτ (h ▸ hσ)
        rw [Function.update_of_ne hne, smul_smul, projA_comm hne, mul_smul, hw σ hσ]
  obtain ⟨z, hz, w, hw⟩ := step Finset.univ
  exact ⟨w, z, hz, fun τ a ha => by rw [projA_eq ha]; exact hw τ (Finset.mem_univ _)⟩

end GlobalTheory.HighWt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem dualWeyl_rowDeg_dominance (O : Type) [CommRing O] [IsDomain O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, ν t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, ν t := by
  classical
  rw [standardMonomialSpanDomain O N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bideterminantDominance O N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem rename_rowPerm_mem (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (σ : Equiv.Perm (Fin N))
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f ∈ dualWeyl O N N ν := by
  classical
  have h : (rename (fun v : Fin N × Fin N => (σ v.1, v.2)) : MvPolynomial (Fin N × Fin N) O →ₐ[O] _) =
      rowAct O (Matrix.of fun a b : Fin N => if σ a = b then (1 : O) else 0) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct]
  rw [h]
  exact dualWeylRowStable O N N ν _ f hf

theorem weight_rowW_eq_rowDeg {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Ne.symm hb]
  · simp

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

open MvPolynomial Formalism.GradedWeylDivisibility

theorem sum_fin_lt_one {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) : ∑ b : Fin N with b.val < 1, g b = g ⟨0, h⟩ := by
  rw [Finset.sum_eq_single_of_mem (⟨0, h⟩ : Fin N) (by simp)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem sum_fin_split_last {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) :
    ∑ b : Fin N, g b = ∑ b : Fin N with b.val < N - 1, g b + g ⟨N - 1, by omega⟩ := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin N => b.val < N - 1)]
  congr 1
  rw [Finset.sum_eq_single_of_mem (⟨N - 1, by omega⟩ : Fin N) (by simp; omega)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem jointWt_bounds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧
      ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  intro O _ _ _ _ N ι _ _ lam _ Gm _ _ w hw τ
  classical
  obtain ⟨z, hz0, hz⟩ := hw
  obtain ⟨a0, ha0, -⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ (w τ)
  have hmem : a0 ∈ alg O N lam := Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha0⟩)
  have hex : ∃ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have ha0z : a0 = 0 := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
      rw [ha0 x 0 (by simp [hne x])]
      exact MultilinearMap.map_coord_zero _ τ (by simp)
    have h1 := hz τ ⟨a0, hmem⟩ ha0
    have h0 : (⟨a0, hmem⟩ : alg O N lam) = 0 := Subtype.ext ha0z
    rw [h0, zero_smul] at h1
    exact hz0 h1.symm
  obtain ⟨x, hx⟩ := hex
  set f := weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) with hfdef
  have hfmem : f ∈ dualWeyl O N N (res N (lam τ)) := dualWeylRowGraded O N N _ _ _ (x τ).2
  have hfhom : IsWeightedHomogeneous (rowW N N) f (w τ) := weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨m, hm⟩ := support_nonempty.2 hx
  have hrd : ∀ a, rowDeg m a = w τ a := fun a => by
    rw [← weight_rowW_eq_rowDeg, hfhom (mem_support_iff.1 hm)]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (∀ k : ℕ, (∑ b : Fin N with b.val < k, w τ (σ.symm b)) ≤ ∑ t : Fin N with t.val < k, res N (lam τ) t) ∧
      ∑ b : Fin N, w τ (σ.symm b) = ∑ t : Fin N, res N (lam τ) t := by
    intro σ
    let e : Fin N × Fin N → Fin N × Fin N := fun v => (σ v.1, v.2)
    have he : Function.Injective e := by
      intro u v huv
      simp only [e, Prod.mk.injEq] at huv
      exact Prod.ext (σ.injective huv.1) huv.2
    have hm' : m.mapDomain e ∈ (rename e f).support := by
      rw [mem_support_iff, coeff_rename_mapDomain e he]
      exact mem_support_iff.1 hm
    have hrd' : ∀ b, rowDeg (m.mapDomain e) b = w τ (σ.symm b) := by
      intro b
      rw [← hrd]
      unfold rowDeg
      refine Finset.sum_congr rfl fun s _ => ?_
      have : (b, s) = e (σ.symm b, s) := by simp [e]
      rw [this, Finsupp.mapDomain_apply_of_injective he]
    have hd := dualWeyl_rowDeg_dominance O N _ _ (rename_rowPerm_mem O N _ σ f hfmem) _ hm'
    simp only [hrd'] at hd
    exact hd
  have hres : ∀ t : Fin N, res N (lam τ) t = lam τ t := fun t => rfl
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · have h := (key (Equiv.refl _)).2
    simpa [hres] using h
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    obtain ⟨h1, h2⟩ := key (Equiv.swap ⟨N - 1, by omega⟩ a)
    have h3 := h1 (N - 1)
    rw [sum_fin_split_last hN, sum_fin_split_last hN] at h2
    have h4 : w τ ((Equiv.swap ⟨N - 1, by omega⟩ a).symm ⟨N - 1, by omega⟩) = w τ a := by simp
    rw [h4] at h2
    have h5 : res N (lam τ) ⟨N - 1, by omega⟩ = lam τ (N - 1) := rfl
    rw [h5] at h2
    omega
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have h1 := (key (Equiv.swap ⟨0, hN⟩ a)).1 1
    rw [sum_fin_lt_one hN, sum_fin_lt_one hN] at h1
    have h2 : w τ a ≤ res N (lam τ) ⟨0, hN⟩ := by simpa using h1
    exact h2

end GlobalTheory.HighWt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.translate_dual_number_point_inverse_constant_tangent : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (S : Type) [CommRing S] (A : Over (Sp S)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (c : epsR S ⟶ A) (p : Sp S ⟶ A.left), c.left = spMap (algebraMap S (DualNumber S)) ≫ p → ∀ y : epsR S ⟶ A, (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧ ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  first | exact @GlobalTheory.TanAdd.translate_const | exact GlobalTheory.TanAdd.translate_const | (intros; apply GlobalTheory.TanAdd.translate_const <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp


theorem _root_.GlobalTheory.T.mem_modelInterior_of_mem_abelianLocus_pullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (S : Scheme.{0}) (f : S ⟶ Y.X) (G : SAB H S), SABMap G Y.t f → ∀ s : S, s ∈ abLocus G.G → f s ∈ (LogKS.interior Y : Set Y.X) := by
  first | exact @GlobalTheory.AbInterior.mem_interior_of_mem_abLocus | exact GlobalTheory.AbInterior.mem_interior_of_mem_abLocus | (intros; apply GlobalTheory.AbInterior.mem_interior_of_mem_abLocus <;> assumption)
end
