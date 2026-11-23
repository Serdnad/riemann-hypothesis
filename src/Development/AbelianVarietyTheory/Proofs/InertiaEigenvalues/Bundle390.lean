module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle348
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle349
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle004
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCyclicGeneratorLamPowerQuotient
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle003
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresCutCocycleLocalCoefficient
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresOfInjectiveEquivariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem map_blocks_of_map_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Aof M).map f = 1 ∧ (Bof M).map f = 0 ∧ (Cof M).map f = 0 := by
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Aof, blk, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, Sum.inl.injEq]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inr j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Bof, blk, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inr i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Cof, blk, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]

theorem map_Scof_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Scof M).map f = 1 := by
  obtain ⟨hA, hB, hC⟩ := map_blocks_of_map_eq_one f M h
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) R) (Q : Matrix (Fin b) (Fin c) R),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  rw [Scof, Matrix.map_sub _ (map_sub f), hmul, hmul, hA, hB, hC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.mkGL_Scof_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
  intro E _ _ m r S x hx _ w hw
  have h1 := hx w hw
  set f := (pLoc E w).comp (pFin E)
  have hM : (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map f = 1 := by
    have := Units.ext_iff.mp h1
    simpa using this
  have hS := map_Scof_eq_one f _ hM
  by_cases hu : IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  · refine Units.ext ?_
    change ((mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      GL (Fin (m + 1)) (Ad E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map f = 1
    rw [coe_mkGL hu]
    exact hS
  · rw [mkGL, dite_eq_right hu, map_one]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem fst_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : (idemS S : Ad E).1 = 1 := rfl

open Classical in
theorem pLoc_pFin_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w (pFin E (idemS S)) = if w ∈ S then 1 else 0 := rfl

theorem prS_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        idemS S * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem prO_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prO S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        (1 - idemS S) * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem pLoc_pFin_idemS_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (pFin E (idemS S)) = 0 := by
  classical
  rw [pLoc_pFin_idemS]; simp [hw]

theorem pLoc_pFin_one_sub_idemS_of_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) :
    pLoc E w (pFin E (1 - idemS S)) = 0 := by
  classical
  rw [map_sub, map_sub, map_one, map_one, pLoc_pFin_idemS]; simp [hw]

theorem one_sub_idemS_mul_eq_zero {S : Finset (HeightOneSpectrum (𝓞 E))} {x : Ad E}
    (h : ∀ w ∉ S, pLoc E w (pFin E x) = 0) : (1 - idemS S) * x = 0 := by
  refine Prod.ext ?_ (Subtype.ext (funext fun w => ?_))
  · change (1 - (idemS S : Ad E).1) * x.1 = 0
    rw [fst_idemS, sub_self, zero_mul]
  · change pLoc E w (pFin E ((1 - idemS S) * x)) = pLoc E w (pFin E 0)
    rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hw : w ∈ S
    · rw [pLoc_pFin_one_sub_idemS_of_mem hw, zero_mul]
    · rw [h w hw, mul_zero]

theorem pLoc_pFin_one_apply (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (i j : Fin a) :
    pLoc E w (pFin E ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem pLoc_pFin_apply_of_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) (i j : Fin a) :
    pLoc E w (pFin E ((g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  have h := congrArg (fun x : GL (Fin a) (w.adicCompletion E) => (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) (hg w hw)
  exact h

theorem one_sub_idemS_mul_sub_eq_zero {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (i j : Fin a) :
    (1 - idemS S) * ((g : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0 :=
  one_sub_idemS_mul_eq_zero fun w hw => by
    rw [map_sub, map_sub, pLoc_pFin_apply_of_mem_supS hg hw, pLoc_pFin_one_apply, sub_self]

theorem prS_prO_supS (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  refine ⟨fun g hg => ⟨?_, ?_⟩, fun g w hw => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prS_apply]
    linear_combination (-1 : Ad E) * one_sub_idemS_mul_sub_eq_zero hg i j
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prO_apply]
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
    linear_combination (one_sub_idemS_mul_sub_eq_zero hg i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (pFin E ((prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
    rw [prS_apply, map_add (f := _), map_sub, map_mul, map_mul, map_add (f := _), map_sub, map_mul, map_mul,
      pLoc_pFin_idemS_of_not_mem hw, pLoc_pFin_one_apply]
    ring

end GlobalTheory.SchurExt
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem coe_cornerGL_idemHom_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (1 : Matrix (Fin a) (Fin a) R) i j - e * (1 : Matrix (Fin a) (Fin a) R) i j + e * (g : Matrix (Fin a) (Fin a) R) i j :=
  rfl

theorem cornerGL_idemHom_mem_NA {a : ℕ} (e : Ad E) (he : IsIdempotentElem e) {u : GA E a}
    (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := a)) : cornerGL a (idemHom e he) u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_cornerGL_idemHom_apply, hu.1 i j hij, Matrix.one_apply_ne (ne_of_lt hij).symm]
    ring
  · rw [coe_cornerGL_idemHom_apply, hu.2 i, Matrix.one_apply_eq]
    ring

theorem cornerGL_idemHom_add_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) {i j : Fin a} (hij : i ≠ j) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j +
      ((cornerGL a (idemHom (1 - e) he.one_sub) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (g : Matrix (Fin a) (Fin a) R) i j := by
  rw [coe_cornerGL_idemHom_apply, coe_cornerGL_idemHom_apply, Matrix.one_apply_ne hij]
  ring

theorem superDiag_cornerGL_idemHom_add {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) :
    GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom e he) g) +
      GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom (1 - e) he.one_sub) g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val = i.val + 1 := (Finset.mem_filter.1 hj).2
  have hij : i ≠ j := fun h => by rw [h] at hj'; omega
  exact cornerGL_idemHom_add_apply e he g hij

theorem prS_prO_NA_psiN :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
      ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := a), prS S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ prO S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧
        GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  intro E _ _ _ a S u hu
  refine ⟨cornerGL_idemHom_mem_NA _ _ hu, cornerGL_idemHom_mem_NA _ _ hu, ?_⟩
  unfold GlobalTheory.JSW.psiN
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  exact congrArg (fun x => ((GroundTheory.Global.adelicChar E x : Circle) : ℂ))
    (superDiag_cornerGL_idemHom_add (idemS S) (isIdempotentElem_idemS S) u)

end GlobalTheory.SchurExt
end
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

private theorem period_ring_generic_hodge {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] (hdom : IsDomain O) (hpid : IsPrincipalIdealRing O)
    (hfr : IsFractionRing O LL) {nn : ℕ}
    (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
    {Xs : Type} {n k : ℕ}
    (hinj : Function.Injective (algebraMap O LL))
    (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (M : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (p : Xs) (a : ℕ)
    (z : G → ↥(stdLatG hinj (twistM M θ)).T ⊗[O] ↥(Xq LL lam a)) (f : G → (Fin k → LL) ⧸ stdG O LL k)
    (hχ : χ = θ) (hlam : lam ≠ 0)
    (hfull : ∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ))))
    (hz : ∀ g, iotaW LL lam a k (z g) = f g)
    (hpres : UpperTheory.KN.HasPres LL N (Q := (Fin k → LL) ⧸ stdG O LL k) (fun g => actD (stdLatG hinj M) g) f)
    (hW : ∃ iW : (Fin k → LL) →ₗ[LL] (Fin n → LL), Function.Injective iW ∧
      ∀ g v, iW (((M g).map (algebraMap O LL)).mulVec v) = ((N p g).map (algebraMap O LL)).mulVec (iW v))
    (ψ : G →* Oˣ) (hψ : ∀ g, ψ g = 1)
    (he : ∃ e : Fin n → LL, e ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec e = ((ψ g : Oˣ) : O) • e) :
    tableLineDegreeTwo.IsAdmCoc PD emb lam jT cT (stdLatG hinj (twistM M θ)) ↥(Xq LL lam a) χ z := by
  subst hχ
  obtain ⟨iW, hW1, hW2⟩ := hW
  obtain ⟨e, he1, he2⟩ := he
  obtain ⟨x₀, hx⟩ := UpperTheory.KN.exists_cyclic_generator_lam_power_quotient LL hinj lam a (fun h0 => hlam (hinj (h0.trans (map_zero _).symm)))
  have h3 : UpperTheory.KN.HasPres LL N (fun g => tableLineDegreeTwo.actTw (stdLatG hinj (twistM M χ)) ↥(Xq LL lam a) χ g) z :=
    UpperTheory.KN.hasPres_of_injective_equivariant _ _ _ (iotaW LL lam a k) z f (LiftW.iotaW_injective LL lam a k)
      (fun g u => LiftW.iotaW_actTw hinj lam a M χ g u) hz hpres
  refine ⟨0, fun b _ hb => ?_⟩
  refine UpperTheory.KN.exists_admissible_extension_latticeTensor PD emb lam jT cT N χ χ p (stdLatG hinj (twistM M χ)) ↥(Xq LL lam a) z iW e x₀ rfl hlam
    hfull h3 hW1 (fun g v => ?_) he1 (fun g => ?_) hx b hb
  · refine (congrArg _ (matRep_twistM_apply M χ g v)).trans ?_
    rw [LinearMap.map_smul_of_tower]
    exact congrArg _ (hW2 g v)
  · rw [he2 g, hψ g, Units.val_one, one_smul]

private theorem chi_mul_inv_eq_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹) g = 1 := by
  simp [chiOC]

attribute [-instance] GlobalTheory.AdmLoc.modFun in
theorem _root_.GlobalTheory.T.cocycleExtension_twistedWeilCoefficients_admissible : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π), ∀ (a : ℕ)
      (z' : Br.G D.nbr i w hw → ↥(latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCoc (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (∀ g, iotaW ↥C.LL.1 lam a D.R.r (z' g) = liftQ C.le D.R.r (z g)) →
    tableLineDegreeTwo.IsAdmCoc (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t) (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet _ _ hDec _ z hz a z' _ hz'
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hE := UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition D i r ρ π w hw C hDec
  exact period_ring_generic_hodge (Br.PD D.loc D.nbr i w hw) hdom hdvr.toIsPrincipalIdealRing hG.1.2.2 (embC HW C hA) lam _ _
    Subtype.val_injective (fun x => locOC C (rTwO D.nd i r x)) (locOC C (WpO D.nd i ρ π)) θ (chiT C θ 1) π a z'
    (fun g => liftQ C.le D.R.r (z g)) (LiftW.chiT_one C θ) hlam.ne_zero hSet.2 hz'
    (UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C (WpO D.nd i ρ π) z hz) hE.1 _ (chi_mul_inv_eq_one C)
    (hE.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩))
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
private theorem isAdmCoc_latOne_of_eigenvector_characters {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {Xs : Type} {n : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (θ χ ψ κ κ₁ : G →* Oˣ) (p : Xs)
      (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (a : ℕ)
      (z : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1)
      (hχ : χ = θ) (hψ : ψ = κ * θ) (hκ : κ₁ = 1) (hlam : lam ≠ 0)
      (hM : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = M g 0 0)
      (hfull : ∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ))))
      (hpres : UpperTheory.KN.HasPres LL N (Q := (Fin 1 → LL) ⧸ stdG O LL 1) (fun g => actD (stdLatG hinj M) g) f)
      (hz : ∀ g, iotaC LL lam a (z g) = f g)
      (hu : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ g : Oˣ) : O) • u)
      (he : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ₁ g : Oˣ) : O) • u) :
      tableLineDegreeTwo.IsAdmCoc PD emb lam jT cT (latOne hinj ψ) ↥(Xq LL lam a) χ z := by
  obtain ⟨u, hu0, hu⟩ := hu
  obtain ⟨e, he0, he⟩ := he
  subst hκ
  have hI := UpperTheory.KN.iotaC_injective_and_equivariant hinj M χ ψ lam a hM
  have h3 : UpperTheory.KN.HasPres LL N (fun g => tableLineDegreeTwo.actTw (latOne hinj ψ) ↥(Xq LL lam a) χ g) z :=
    UpperTheory.KN.hasPres_of_injective_equivariant N _ _ (iotaC LL lam a) z f hI.1 hI.2 hz hpres
  obtain ⟨x₀, hx⟩ := UpperTheory.KN.exists_cyclic_generator_lam_power_quotient LL hinj lam a (fun h0 => hlam (hinj (h0.trans (map_zero _).symm)))
  refine ⟨0, fun b _ hb => ?_⟩
  refine UpperTheory.KN.exists_admissible_extension_latticeTensor PD emb lam jT cT N θ χ p (latOne hinj ψ) ↥(Xq LL lam a) z
    (LinearMap.toSpanSingleton LL _ u) e x₀ hχ hlam hfull h3
    (fun s t hst => smul_left_injective LL hu0 hst) (fun g v => ?_) he0 (fun g => ?_) hx b hb
  · rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, Matrix.mulVec_smul, hu g, hψ]
    funext m
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]
    ring
  · rw [he g]
    simp

theorem _root_.GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ c ∈ Finset.Icc 1 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), ∀ (a : ℕ)
      (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g)) →
    tableLineDegreeTwo.IsAdmCoc (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t) (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c))
      ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet _ _ hDec _ c hc z hz a z' _ hz'
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have hpid : IsPrincipalIdealRing ↥(OL C.LL) := hdvr.toIsPrincipalIdealRing
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C (chiRatO D.nd i c) z hz
  have hE := UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition D i r ρ π w hw C hDec
  have hκ : chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹) = 1 := by simp [chiOC]
  have H := isAdmCoc_latOne_of_eigenvector_characters (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
    (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
    (fun x => locOC C (rTwO D.nd i r x)) θ (chiT C θ 1) (chiT C θ c)
    (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) π
    Subtype.val_injective (locOC C (chiRatO D.nd i c)) a z' (fun g => liftQ C.le 1 (z g))
    (chiT_one_eq_theta C θ) rfl hκ hlam.ne_zero (chiT_ratio C θ c) hSet.2 h2 hz' (hE.2 c hc)
    (hE.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩))
  exact H
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; Continuous fun g : ↥(GK K) => TWact (AI.gRW LL (g : GQ l)) T g y := by
  first | exact @GlobalTheory.WeakClosed.continuous_orbit_twTop | exact GlobalTheory.WeakClosed.continuous_orbit_twTop | (intros; apply GlobalTheory.WeakClosed.continuous_orbit_twTop <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory.WeakClosed.SmallW

theorem glue
  (tilt : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), ¬ IsUnit (AI.εroot s - 1) ∧ ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ (AI.εroot s - 1) ^ m)
  (nbhd : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ → (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) → letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l, (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U)
  (witt : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p] (x : WittVector p R) (N m : ℕ), ∃ k : ℕ, ∀ (z : WittVector p R) (n : ℕ), n < N → (x ^ k * z).coeff n ∈ Ideal.span {x.coeff 0 ^ m}) :
  ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ k : ℕ, ∀ z : Ainf l, inclW l ((WittVector.teichmuller l (AI.εroot s) - 1) ^ k * z) ∈ U := by
  intro l _ P AI s
  intro U hU

  obtain ⟨hnu, hdiv⟩ := tilt AI s

  obtain ⟨N, m, hN⟩ := nbhd (AI.εroot s - 1) hnu hdiv U hU

  obtain ⟨k, hk⟩ := witt (WittVector.teichmuller l (AI.εroot s) - 1) N m
  refine ⟨k, fun z => hN _ fun n hn => ?_⟩
  have h0 : (WittVector.teichmuller l (AI.εroot s) - 1 : WittVector l (OCb l)).coeff 0 =
      AI.εroot s - 1 := by
    have h := WittVector.add_coeff_zero
      (WittVector.teichmuller l (AI.εroot s) - 1 : WittVector l (OCb l)) 1
    rw [sub_add_cancel, WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h
    exact eq_sub_of_add_eq h.symm
  simpa [h0] using hk z n hn

theorem main : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ k : ℕ, ∀ z : Ainf l, inclW l ((WittVector.teichmuller l (AI.εroot s) - 1) ^ k * z) ∈ U :=
  glue GlobalTheory.T.epsilonRoot_sub_one_isPseudoUniformizer_tilt GlobalTheory.T.weakly_small_of_not_isUnit_of_dvd_pow GlobalTheory.T.exists_pow_mul_coeff_mem_span_coeff_zero_pow

end GlobalTheory.WeakClosed.SmallW
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.isComplementedSubrep_localMatrixRep_twistedSum : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsSummandTw i w hw r Xs (locU i w hw M hSub.1) := by
  first | exact @GlobalTheory.Pass.LocDual.isSummandTw_locU | exact GlobalTheory.Pass.LocDual.isSummandTw_locU | (intros; apply GlobalTheory.Pass.LocDual.isSummandTw_locU <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem _root_.GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (ϖ : X.O0 i), Irreducible ϖ → ∀ y : ↥(DecV N v) → Fin D.R.r → X.O0 i, (∀ a, IsLocallyConstant fun g => IsLocalRing.residue (X.O0 i) (y g a)) → (∀ g h a, y (g * h) a - (y g a + (Tdual i s g.1).mulVec (y h) a) ∈ IsLocalRing.maximalIdeal (X.O0 i)) → ((∃ y', IsFCoc bkP i v hv ρ y' ∧ ∀ g a, y' g a - y g a ∈ IsLocalRing.maximalIdeal (X.O0 i)) ↔ ∀ d, IsFCoc bkP i v hv (Tgl i s) d → ∃ f : ↥(DecV N v) → Formalism.BasicNotions.KmodO (X.O0 i), IsLocallyConstant f ∧ ∀ g h, (Submodule.Quotient.mk ((algebraMap (X.O0 i) (FractionRing (X.O0 i)) ϖ)⁻¹ * algebraMap (X.O0 i) (FractionRing (X.O0 i)) (d g ⬝ᵥ (Tdual i s g.1).mulVec (y h))) : Formalism.BasicNotions.KmodO (X.O0 i)) = ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i) • f h - f (g * h) + f g) := by
  first | exact @GlobalTheory.BKLatticeCochain.lift_iff_orthogonal | exact GlobalTheory.BKLatticeCochain.lift_iff_orthogonal | (intros; apply GlobalTheory.BKLatticeCochain.lift_iff_orthogonal <;> assumption)
end
