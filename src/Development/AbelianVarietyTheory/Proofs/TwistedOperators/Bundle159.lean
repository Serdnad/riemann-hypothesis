module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle147
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle148
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle133
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

noncomputable def topVec (r : ℕ) (lam : DomWeight r) : nablaSq ℂ r lam :=
  ⟨extremal ℂ r lam, hwMem ℂ r r le_rfl _ (factNatW r lam).1⟩

theorem sqRep_topVec_of_unitriangular (r : ℕ) (lam : DomWeight r) (g : GL (Fin r) ℂ)
    (h1 : (g : Matrix (Fin r) (Fin r) ℂ).BlockTriangular id) (h2 : ∀ a, (g : Matrix (Fin r) (Fin r) ℂ) a a = 1) :
    sqRep ℂ r lam g (topVec r lam) = topVec r lam :=
  Subtype.ext ((factSqHighestWeight ℂ r lam).2 g h1 h2)

theorem sqRep_topVec_diag {m : ℕ} (r : ℕ) (a : Part m) (t : Fin r → ℂˣ) :
    sqRep ℂ r (pad r a) (diagGL ℂ r t) (topVec r (pad r a)) =
      (∏ i, (t i : ℂ) ^ rowNu (r := r) a.1 i) • topVec r (pad r a) := by
  apply Subtype.ext
  have h := (factSqHighestWeight ℂ r (pad r a)).1 t
  have e : ((∏ i, t i ^ (pad r a).w i : ℂˣ) : ℂ) = ∏ i, (t i : ℂ) ^ rowNu (r := r) a.1 i := by
    simp [pad]
  rw [e] at h
  exact h

theorem exists_intertwining_piece (n n' : ℕ) (a : Part (min n n')) :
    ∃ φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
      (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))),
      φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a)) ≠ 0 := by
  obtain ⟨T, hT⟩ := GlobalTheory.Proof.GenericSubmoduleMonomials.exists_pairing n n' (min n n')
  obtain ⟨hE, hN⟩ := GlobalTheory.GLDuality.pairing_equivariant_and_ne_zero n n' (min n n') T hT
  obtain ⟨j, hj, hj0⟩ := GlobalTheory.GLDuality.exists_map_nablaSq_pad n (min n n') (min_le_left _ _) a
  obtain ⟨j', hj', hj0'⟩ := GlobalTheory.GLDuality.exists_map_nablaSq_pad n' (min n n') (min_le_right _ _) a
  refine ⟨⟨TensorProduct.lift (T.compl₁₂ j j'), fun p => ?_⟩, ?_⟩
  · apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply, pieceRep_tmul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    change T (j (sqRep ℂ n _ p.1 v)) (j' (sqRep ℂ n' _ p.2 w)) = matRep n n' (p.1, p.2) (T (j v) (j' w))
    rw [hj, hj', hE]
  · change T (j _) (j' _) ≠ 0
    rw [hj0 _ rfl, hj0' _ rfl]
    exact hN _ _ _

theorem map_topVec_highest (n n' : ℕ) (a : Part (min n n'))
    (φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
      (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)))) :
    φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a)) ∈ dualWeyl ℂ n' n (rowNu (r := n) a.1) ∧
      ∀ i j : Fin n', i < j → ∀ k : ℕ, 1 ≤ k →
        rowDiv ℂ i j k (φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a))) = 0 := by
  have hφ : ∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) v w, matRep n n' (g, h) (φ (v ⊗ₜ w)) =
      φ (sqRep ℂ n _ g v ⊗ₜ sqRep ℂ n' _ h w) := fun g h v w => by
    have := Representation.IntertwiningMap.isIntertwining _ _ φ (g, h) (v ⊗ₜ w)
    rw [pieceRep_tmul] at this
    exact this.symm
  refine ⟨GlobalTheory.GLDuality.mem_dualWeyl_of_unitriangular_fixed n n' _ _ (fun g h1 h2 => ?_) (fun t => ?_), GlobalTheory.GLDuality.rowDiv_eq_zero_of_matRep_unipotent_fixed n n' _ fun g h1 h2 => ?_⟩
  · rw [hφ, sqRep_topVec_of_unitriangular _ _ g h1 h2, map_one, Module.End.one_apply]
  · rw [hφ, sqRep_topVec_diag, map_one, Module.End.one_apply, ← TensorProduct.smul_tmul', map_smul]
  · rw [hφ, sqRep_topVec_of_unitriangular _ _ g h1 h2, map_one, Module.End.one_apply]

theorem colAdd_matRep_diag {n n' : ℕ} (t : Fin n → ℂˣ) (l j : Fin n) (c : ℂ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    colAdd ℂ l j c (matRep n n' (diagGL ℂ n t, 1) v) =
      matRep n n' (diagGL ℂ n t, 1) (colAdd ℂ l j (c * t j * (t l)⁻¹) v) := by
  have hX : ∀ (a : Fin n') (s : Fin n),
      sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ
        (X (a, s)) = C (t s : ℂ) * X (a, s) := by
    intro a s
    rw [← matRep_apply, matRep_X]
    simp [diagGL, Matrix.one_apply, Matrix.diagonal_apply, apply_ite C]
  have e : (colAdd ℂ (r := n') l j c).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ).comp
        (colAdd ℂ l j (c * t j * (t l)⁻¹)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hX]
    by_cases hs : s = j
    · subst hs
      simp only [colAdd, map_mul, algHom_C, aeval_X, if_true, map_add (f := _), hX, algebraMap_eq]
      have : (C ((t l)⁻¹ : ℂ) : MvPolynomial (Fin n' × Fin n) ℂ) * C (t l : ℂ) = 1 := by
        rw [← map_mul]; simp
      simp only [Units.val_inv_eq_inv_val] at this ⊢
      linear_combination (-(C c * C (t s : ℂ) * X (a, l))) * this
    · simp only [colAdd, map_mul, algHom_C, aeval_X, if_neg hs, hX, algebraMap_eq]
  exact DFunLike.congr_fun e v

theorem exists_mem_dualWeyl_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), v ∈ N ∧ v ≠ 0 ∧ v ∈ dualWeyl ℂ n' n ν := by
  classical
  obtain ⟨v, hv, hv0, hf⟩ := GlobalTheory.GLDuality.exists_colAdd_fixed_of_stable n n' N hN hst
  let M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ) :=
    { carrier := {w | w ∈ N ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c w = w}
      add_mem' := fun ha hb => ⟨N.add_mem ha.1 hb.1, fun l j h c => by rw [map_add (f := _), ha.2 l j h, hb.2 l j h]⟩
      zero_mem' := ⟨N.zero_mem, fun l j h c => map_zero _⟩
      smul_mem' := fun a _ ha => ⟨N.smul_mem a ha.1, fun l j h c => by rw [map_smul, ha.2 l j h]⟩ }
  have hM : ∀ t : Fin n → ℂˣ, ∀ w ∈ M, matRep n n' (diagGL ℂ n t, 1) w ∈ M := fun t w hw =>
    ⟨hst _ w hw.1, fun l j h c => by rw [colAdd_matRep_diag, hw.2 l j h]⟩
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hv0
  have hw := GlobalTheory.GLDuality.weightedHomogeneousComponent_colW_mem n n' M hM (Finsupp.weight (colW n' n) d) v ⟨hv, hf⟩
  refine ⟨_, _, hw.1, ne_zero_iff.2 ⟨d, ?_⟩, (dualWeylPoint ℂ n' n _ _).2
    ⟨weightedHomogeneousComponent_isWeightedHomogeneous _ _, hw.2⟩⟩
  rwa [coeff_weightedHomogeneousComponent, if_pos rfl]

theorem exists_highest_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ N, matRep n n' p v ∈ N) :
    ∃ (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), v ∈ N ∧ v ≠ 0 ∧ v ∈ dualWeyl ℂ n' n ν ∧
      ∀ i j : Fin n', i < j → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ i j k v = 0 := by
  obtain ⟨ν, v, hv, hv0, hvd⟩ := exists_mem_dualWeyl_of_stable n n' N hN fun g => hst (g, 1)
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n') ℂ, ∀ f ∈ N ⊓ dualWeyl ℂ n' n ν,
      rowAct ℂ u f ∈ N ⊓ dualWeyl ℂ n' n ν := by
    intro u hu f hf
    refine ⟨?_, dualWeylRowStable ℂ n' n ν u f hf.2⟩
    have h1 := hst (1, unitaryIncl n' (Matrix.UnitaryGroup.transpose ⟨u, hu⟩)) f hf.1
    rw [matRep_one_left] at h1
    exact h1
  obtain ⟨w, hw, hw0, hk⟩ := exists_killed_of_rowDivClosed _
    (rowDivClosed_of_rowAct_stable _ (rowAct_mem_of_unitary_stable _ hU))
    (fun e => hv0 ((Submodule.eq_bot_iff _).1 e v ⟨hv, hvd⟩))
  exact ⟨ν, w, hw.1, hw0, hw.2, hk⟩

theorem nonempty_equiv_polyRep (n n' : ℕ) :
    Nonempty ((Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).Equiv
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)))) := by
  classical
  have h1 := irreducibleDistinct_gl (min_le_left n n')
  have h2 := irreducibleDistinct_gl (min_le_right n n')
  have hirr : ∀ a : Part (min n n'),
      (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IsIrreducible :=
    fun a => GlobalTheory.OuterTensor.isIrreducible_outer_tprod _ _ _ _ _ _ (h1.1 a) (h2.1 a)
  have hdis : ∀ a b : Part (min n n'), a ≠ b →
      ∀ φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
        (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) b), φ = 0 := by
    intro a b hab
    refine GlobalTheory.outerTensor_intertwining_eq_zero_of_left _ _ _ _ _ _ _ _ _ _ fun ψ => ?_
    have := h1.1 a
    have := h1.1 b
    refine (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_left fun hb => hab (h1.2 a b ?_)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ψ.toLinearMap hb) ψ.isIntertwining'⟩
  choose φ hφ using exists_intertwining_piece n n'
  let Φ : (Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))) :=
    ⟨DirectSum.toModule ℂ _ _ (fun i => (φ i).toLinearMap), fun g => by
      refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun v => ?_
      simp [(φ i).isIntertwining]⟩
  have hΦ : ∀ i v, Φ (DirectSum.lof ℂ _ _ i v) = φ i v := fun i v =>
    DirectSum.toModule_lof ℂ (φ := fun i => (φ i).toLinearMap) i v
  have hinj : Function.Injective Φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    refine GlobalTheory.directSum_eq_zero_of_toModule_eq_zero _ _ hirr hdis Φ ?_ (DFinsupp.support x) x
      (fun j hj => DFinsupp.notMem_support_iff.1 hj) hx
    intro i v hv
    have := hirr i
    have hi := (Representation.IsIrreducible.injective_or_eq_zero (φ i)).resolve_right
      (fun e => hφ i (by rw [e]; rfl))
    apply hi
    rw [← hΦ, hv, map_zero]
  have hsurj : Function.Surjective Φ.toLinearMap := by
    rw [← LinearMap.range_eq_top]
    by_contra hM
    obtain ⟨N, hN, hNM, hst⟩ := GlobalTheory.GLDuality.Compl.exists_stable_disjoint n n' _ hM (by
      rintro p _ ⟨x, rfl⟩
      exact ⟨_, Representation.IntertwiningMap.isIntertwining _ _ Φ p x⟩)
    obtain ⟨ν, v, hv, hv0, hvd, hk⟩ := exists_highest_of_stable n n' N hN hst
    obtain ⟨a, rfl⟩ := (GlobalTheory.GLDuality.HighestLine.highest_line n' n ν v hvd hk hv0).1
    obtain ⟨ht1, ht2⟩ := map_topVec_highest n n' a (φ a)
    obtain ⟨c, hc⟩ := (GlobalTheory.GLDuality.HighestLine.highest_line n' n _ _ ht1 ht2 (hφ a)).2 v hvd hk
    refine hv0 ((Submodule.eq_bot_iff _).1 hNM v ⟨hv, ?_⟩)
    rw [hc]
    exact Submodule.smul_mem _ _ ⟨_, hΦ a _⟩
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩) Φ.isIntertwining'⟩

end GlobalTheory.GLDuality

theorem GlobalTheory.Published.glHoweDuality_holds : GlobalTheory.Published.GLHoweDuality :=
  GlobalTheory.Published.glHoweDuality_of_equiv fun n n' _ _ => GlobalTheory.GLDuality.nonempty_equiv_polyRep n n'
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceIdem

variable {D : D7}

theorem AF_ext {F : Type} [Field F] [NumberField F] {x y : AF F} (h1 : fstA F x = fstA F y)
    (h2 : sndA F x = sndA F y) : x = y := Prod.ext h1 h2

theorem fstA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : fstA F (pairA F a b) = a := rfl

theorem sndA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : sndA F (pairA F a b) = b := rfl

theorem placeIdem_eq_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε = pairA D.host.F 0 (singleV D.host.F v 1) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  change evalV D.host.F u α = evalV D.host.F u (singleV D.host.F v 1)
  by_cases huv : u = v
  · subst huv; rw [h1, (hsv u).2.1]
  · rw [h0 u huv, (hsv v).2.2 u huv]

theorem single_mul_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) :
    pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 (singleV D.host.F w 1) = 0 := by
  refine AF_ext ?_ ?_
  · rw [map_mul, fstA_pairA, fstA_pairA, map_zero, mul_zero]
  · rw [map_mul, sndA_pairA, sndA_pairA, map_zero]
    refine Subtype.ext (funext fun u => ?_)
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F w 1) = evalV D.host.F u 0
    rw [map_mul, map_zero]
    by_cases huv : u = v
    · subst huv; rw [(hsv w).2.2 u hvw, mul_zero]
    · rw [(hsv v).2.2 u huv, zero_mul]

theorem finPart_algebraMap (x : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) x) = sndA D.host.F x ⊗ₜ[D.host.F] (1 : D.host.E) := by
  change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (algebraMap (AF D.host.F) (AE D) x) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl


theorem exists_idem_half : ∀ (D : D7), ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧ finPart D e ∈ intAE D ∧
    finPart D (cA D e) ∈ intAE D ∧ ∃ h : AE D, finPart D h ∈ intAE D ∧ 2 * h = 1 - e - cA D e := by
  intro D
  obtain ⟨P, hP2, hsv, β, hβ, h1⟩ := GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul D.host.F
  have H : ∀ v ∈ P, ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    obtain ⟨e, ε, he, hε, hs⟩ := Formalism.IndefR.Fin.twoSplitIdem D v (hP2 v hv)
    exact ⟨e, he.1, he.2.1, by rw [hs, placeIdem_eq_single hsv hε]⟩
  choose! E hEE hEc hEs using H
  have absE : ∀ v ∈ P, E v = E v * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv; rw [← hEs v hv, mul_add, hEE v hv, hEc v hv, add_zero]
  have absC : ∀ v ∈ P, cA D (E v) = cA D (E v) * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    rw [← hEs v hv, mul_add, mul_comm (cA D (E v)) (E v), hEc v hv, ← map_mul, hEE v hv, zero_add]
  have cross : ∀ (x y : AE D) (v w : HeightOneSpectrum (𝓞 D.host.F)), v ≠ w →
      x = x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) →
      y = y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1)) → x * y = 0 := by
    intro x y v w hvw hx hy
    calc x * y = (x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))) *
          (y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1))) := by rw [← hx, ← hy]
      _ = x * y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1) *
          pairA D.host.F 0 (singleV D.host.F w 1)) := by rw [map_mul]; ring
      _ = 0 := by rw [single_mul_single hsv hvw, map_zero, mul_zero]
  have hee : (∑ v ∈ P, E v) * (∑ v ∈ P, E v) = ∑ v ∈ P, E v := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absE w hw))
      (fun h => absurd hv h), hEE v hv]
  have hec : (∑ v ∈ P, E v) * cA D (∑ v ∈ P, E v) = 0 := by

    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absC w hw))
      (fun h => absurd hv h), hEc v hv]
  have hsum : (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) =
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
    have hcs : cA D (∑ v ∈ P, E v) = ∑ v ∈ P, cA D (E v) := map_sum (cA D) E P
    calc (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) = (∑ v ∈ P, E v) + ∑ v ∈ P, cA D (E v) := congrArg (fun z => (∑ v ∈ P, E v) + z) hcs
      _ = ∑ v ∈ P, (E v + cA D (E v)) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ P, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) :=
          Finset.sum_congr rfl fun v hv => hEs v hv
      _ = algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := (map_sum _ _ _).symm
  have hi1 : finPart D (∑ v ∈ P, E v) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans (congrArg (finPart D) hee))
  have hi2 : finPart D (cA D (∑ v ∈ P, E v)) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans
      (congrArg (finPart D) ((map_mul (cA D) _ _).symm.trans (congrArg (cA D) hee))))
  refine ⟨∑ v ∈ P, E v, hee, hec, hi1, hi2, ?_⟩
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β), ?_, ?_⟩
  · rw [finPart_algebraMap, sndA_pairA]
    exact AddSubgroup.subset_closure ⟨β, hβ, 1, by simp⟩
  · have key : 2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β =
        1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1) := by
      refine AF_ext ?_ ?_
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sub, map_sum, map_one, map_ofNat, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, sub_zero]
        rw [← map_ofNat (algebraMap D.host.F (Ainf D.host.F)) 2, ← map_mul]
        norm_num
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sub, map_sum, map_one, map_ofNat, sndA_pairA]
        simp only [sndA_pairA]
        linear_combination -h1
    calc (2 : AE D) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β)
        = algebraMap (AF D.host.F) (AE D) (2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β) := by
          rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) 2 from (map_ofNat _ 2).symm]
          exact (map_mul _ _ _).symm
      _ = algebraMap (AF D.host.F) (AE D) (1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) :=
          congrArg _ key
      _ = 1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
          rw [map_sub, map_one]
      _ = 1 - ((∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v)) := by rw [hsum]
      _ = 1 - ∑ v ∈ P, E v - cA D (∑ v ∈ P, E v) := by rw [sub_sub]

end GlobalTheory.TwoPlaceIdem
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  first | exact @GlobalTheory.InvTransposeIso.grp_contra | exact GlobalTheory.InvTransposeIso.grp_contra | (intros; apply GlobalTheory.InvTransposeIso.grp_contra <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_open_eq_one_of_continuous_mul_finitePoints : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  first | exact @GlobalTheory.OpenKer.eq_one_on_finite_of_mul | exact GlobalTheory.OpenKer.eq_one_on_finite_of_mul | (intros; apply GlobalTheory.OpenKer.eq_one_on_finite_of_mul <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemUnder

theorem under_eq_of_isIdemAt : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), Formalism.L2.NTheta.IsIdemAt e PP → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := by
  intro D e PP v ε he hv hsum

  obtain ⟨hee, hec, -⟩ := he.1
  have hfix : e * algebraMap (AF D.host.F) (AE D) ε = e := by
    rw [← hsum, mul_add, hee, hec, add_zero]

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hone : Φ e PP = 1 := (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he).2.1
  by_contra hne
  have hzero := (GlobalTheory.IdemSupport.place_comp hΦ hv).2.2 PP hne
  have hcomp := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (algebraMap (AF D.host.F) (AE D) ε) PP
  rw [hfix, hzero, mul_zero, hone] at hcomp
  exact one_ne_zero hcomp

end GlobalTheory.IdemUnder
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult MeasureTheory NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodRowsLevel

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_lev_of_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {x : GL (Fin (Yc D 0).rank) (EAf D)}
    (hx : x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      levFn (R.βY 0) (R.dat0 P) x = levFn (R.βY 0) (R.dat0 R.triv) x := by
  have h1 : rTup (R.βY 0) (R.dat0 R.triv) x = 1 := Subgroup.mem_bot.1 hx.2
  have h1' : rTup (R.βY 0) (R.dat0 P) x = 1 := h1
  refine ⟨⟨hx.1, ?_⟩, ?_⟩
  · rw [h1']; exact Subgroup.one_mem _
  · unfold levFn
    rw [h1, h1', blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]
    rfl

theorem isMultMap_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {S : MMap (R.MY 0)}
    (h : IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S) :
    IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) S := by
  refine ⟨h.aut, h.cusp, ?_, h.equiv, h.cont⟩
  intro v k hk g
  have hk2 : k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)).comap (finE (Yc D 0)) := hk
  rw [Subgroup.mem_inf, Subgroup.mem_comap] at hk2
  have hm := mem_lev_of_triv R P hk2.2
  have hk' : k ∈ levS _ (R.βY 0) (R.dat0 P) :=
    (show k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) from
      Subgroup.mem_inf.2 ⟨hk2.1, Subgroup.mem_comap.2 hm.1⟩)
  rw [h.lev v k hk' g]
  simp only [levChi]
  rw [hm.2]

theorem eeat_le_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) : R.EEat P ≤ R.EEat R.triv := by
  intro S hS
  rw [RealDat.EEat, goodPart, Submodule.mem_inf] at hS ⊢
  refine ⟨?_, hS.2⟩
  exact Submodule.span_mono (fun S' hS' => isMultMap_triv R P hS') hS.1

theorem eeat_sub_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → (∀ P, R.EEat P ≤ R.EEat R.triv) ∧ (∀ P, R.EEat P ≤ LinearMap.range R.HE.e) ∧ ∀ P, ∀ S ∈ R.EEat P, ∀ S' ∈ R.EEat P, IsMultIP (R.MY 0) R.ν0 R.fd0 S S' (ipM (R.MY 0) R.ν0 R.fd0 S S') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM
  have h2 : ∀ P, R.EEat P ≤ LinearMap.range R.HE.e := fun P => by
    rw [hM.HE.2.1]; exact eeat_le_triv R P
  refine ⟨eeat_le_triv R, h2, ?_⟩
  intro P S hS S' hS'
  obtain ⟨x, rfl⟩ := h2 P hS
  obtain ⟨y, rfl⟩ := h2 P hS'
  rw [← hM.HE.2.2 x y]
  exact GlobalTheory.SchurPolar.isMultiplicityInner_inner (R.MY 0) R.ν0 R.fd0 R.HE _ hM.HE x y

end GlobalTheory.GoodRowsLevel
end
