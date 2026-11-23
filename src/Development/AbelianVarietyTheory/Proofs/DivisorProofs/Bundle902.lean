module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobRigKer

variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]


variable (O A) in
def evalZeroTwo : A ⊗[O] A →ₗ[O] O :=
  (TensorProduct.lid O O).toLinearMap ∘ₗ TensorProduct.map (counit (R := O)) (counit (R := O))

@[simp] theorem evalZeroTwo_tmul (a b : A) :
    evalZeroTwo O A (a ⊗ₜ b) = counit (R := O) a * counit (R := O) b := by
  simp [evalZeroTwo]

theorem evalZeroTwo_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    evalZeroTwo O B (pullbackTwo f c) = evalZeroTwo O A c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo, evalZeroTwo_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]

theorem evalZeroTwo_comul (b : A) : evalZeroTwo O A (comul b) = counit (R := O) b := by
  have key : TensorProduct.map (counit (R := O)) (counit (R := O)) (comul (R := O) b) =
      LinearMap.lTensor O (counit (R := O)) (LinearMap.rTensor A (counit (R := O)) (comul b)) := by
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  show TensorProduct.lid O O (TensorProduct.map (counit (R := O)) (counit (R := O)) (comul b)) = _
  rw [key, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul, one_smul]

theorem evalZeroTwo_cobOne (b : A) : evalZeroTwo O A (cobOne O A b) = - counit (R := O) b := by
  rw [cobOne_apply, map_sub, map_sub, evalZeroTwo_comul, evalZeroTwo_tmul, evalZeroTwo_tmul,
    Bialgebra.counit_one]
  ring

theorem mk_kerIdeal_apply (f : A →ₐc[O] B) (a : A) :
    Ideal.Quotient.mkₐ O (kerIdeal f) (f a) = counit (R := O) a • 1 := by
  have hmem : a - algebraMap O A (counit (R := O) a) ∈ augIdeal O A := by
    simp [RingHom.mem_ker]
  have himg := Ideal.mem_map_of_mem (f : A →ₐ[O] B) hmem
  have e : (f : A →ₐ[O] B) (algebraMap O A (counit (R := O) a)) = algebraMap O B (counit (R := O) a) :=
    AlgHom.commutes _ _
  rw [map_sub, e] at himg
  rw [Algebra.smul_def, mul_one, ← AlgHom.commutes (Ideal.Quotient.mkₐ O (kerIdeal f)),
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  exact himg

theorem map_mk_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (pullbackTwo f c) = evalZeroTwo O A c • 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [pullbackTwo, TensorProduct.map_tmul, BialgHom.coe_toLinearMap,
      Algebra.TensorProduct.map_tmul, mk_kerIdeal_apply, evalZeroTwo_tmul,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [mul_comm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), add_smul]

theorem map_mk_cobOne_eq_zero (f : A →ₐc[O] B) {c : A ⊗[O] A} {b : B}
    (hb : counit (R := O) b = 0) (hc : cobOne O B b = pullbackTwo f c) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (cobOne O B b) = 0 := by
  rw [hc, map_mk_pullTwo, ← evalZeroTwo_pullTwo f c, ← hc, evalZeroTwo_cobOne, hb, neg_zero,
    zero_smul]

def oneFun {p : ℕ} (G : PDivGroup p O) : G.funs := ⟨fun _ => 1, fun _ => map_one _⟩

theorem funsMap_oneFun {p : ℕ} {G H : PDivGroup p O} (f : G ⟶ H) :
    funsMap f (oneFun H) = oneFun G :=
  Subtype.ext (funext fun n => map_one (f.app n))

theorem dUnit_one : dUnit (R := O) (1 : A) = 0 := by
  simp [dUnit]

end GlobalTheory.PDiv.FrobRigKer

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv.FrobRigKer

theorem ker_rigExtMap_relFrob_le_range_rigOfOmega (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hmk : Function.Surjective (frobTwist h G).rigMk := Submodule.mkQ_surjective _
  obtain ⟨⟨c, w⟩, rfl⟩ := hmk x
  rw [rigExtMap_mk] at hx
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
  have hB1 : G.cob B = cocyclesMap (relFrob h G) c := congrArg Prod.fst hB
  have hB2 : G.dFun B = G.omegaMap _ (relFrob h G) w := congrArg Prod.snd hB
  set t : K := counit (R := K) (B.1 1) with ht
  set B₁ : G.funs := B - t • oneFun G with hB₁
  set c₁ : (frobTwist h G).cocycles := c - t • (frobTwist h G).cob (oneFun (frobTwist h G))
    with hc₁def
  have hc₁ : G.cob B₁ = cocyclesMap (relFrob h G) c₁ := by
    simp only [hB₁, hc₁def, map_sub, map_smul, hB1, cocyclesMap_cob, funsMap_oneFun]
  have hb0 : counit (R := K) (B₁.1 1) = 0 := by
    show counit (R := K) (B.1 1 - t • (1 : G.A 1)) = 0
    rw [map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, ht, sub_self]
  have hbd : dUnit (R := K) (B₁.1 1) = 0 := by
    have e1 : G.dFun B = 0 := by rw [hB2, omegaMap_relFrob, LinearMap.zero_apply]
    have e2 : G.dFun (oneFun G) = 0 := Subtype.ext (funext fun n => dUnit_one)
    have e : G.dFun B₁ = 0 := by rw [hB₁, map_sub, map_smul, e1, e2, smul_zero, sub_zero]
    exact congrArg (fun z : G.omega => z.1 1) e
  have hcob : cobOne K (G.A 1) (B₁.1 1) = pullbackTwo ((relFrob h G).app 1) (c₁.1 1) :=
    congrArg (fun z : G.cocycles => z.1 1) hc₁
  have hker := GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G 1
  have hmem : B₁.1 1 ∈ frobKerIdeal p K (G.A 1) := by
    refine GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential p K (G.A 1) _ hb0 hbd ?_
    rw [hker]
    exact map_mk_cobOne_eq_zero ((relFrob h G).app 1) hb0 hcob
  rw [hker] at hmem
  have hV : (verschiebung h G).app 1 (B₁.1 1) = 0 :=
    GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) _ hmem
  have hcomp : cocyclesMap (verschiebung h G) (cocyclesMap (relFrob h G) c₁) =
      cocyclesMap (verschiebung h G ≫ relFrob h G) c₁ :=
    Subtype.ext (funext fun n => (pullTwo_comp _ _ _).symm)
  obtain ⟨B', hB'⟩ : c₁ ∈ LinearMap.range (frobTwist h G).cob := by
    refine GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP (frobTwist h G) c₁ (funsMap (verschiebung h G) B₁) ?_ hV
    rw [← cocyclesMap_cob, hc₁, hcomp, verschiebung_comp_relFrob]
  set B₀ : (frobTwist h G).funs := B' + t • oneFun (frobTwist h G) with hB₀
  have hc0 : (frobTwist h G).cob B₀ = c := by
    rw [hB₀, map_add (f := _), map_smul, hB', hc₁def, sub_add_cancel]
  refine ⟨w - (frobTwist h G).dFun B₀, ?_⟩
  show Submodule.Quotient.mk ((0 : (frobTwist h G).cocycles), w - (frobTwist h G).dFun B₀) =
    Submodule.Quotient.mk (c, w)
  refine ((Submodule.Quotient.eq
    (LinearMap.range ((frobTwist h G).cob.prod (frobTwist h G).dFun))).2
    (LinearMap.mem_range.2 ⟨B₀, Prod.ext ?_ ?_⟩)).symm
  · show (frobTwist h G).cob B₀ = c - 0
    rw [sub_zero]
    exact hc0
  · show (frobTwist h G).dFun B₀ = w - (w - (frobTwist h G).dFun B₀)
    exact (sub_sub_cancel w _).symm

end GlobalTheory.PDivGroup
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

namespace GlobalTheory.WachChain

theorem cancel_left {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O)
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin q) (Fin m) O} (h : A * X = A * Y) : X = Y := by
  ext i j
  have h1 := congrArg (fun Z => Z *ᵥ Pi.single j 1) h
  simp only [← Matrix.mulVec_mulVec] at h1
  have h2 := congrFun (hA h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem solve {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O) (Z : Matrix ι (Fin m) O)
    (h : ∀ j, ∃ w, A *ᵥ w = fun i => Z i j) : ∃ Y : Matrix (Fin q) (Fin m) O, A * Y = Z := by
  choose w hw using h
  refine ⟨Matrix.of fun k j => w j k, ?_⟩
  ext i j
  have h1 := congrFun (hw j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1

theorem mkRep {Γ O ι : Type} [Group Γ] [CommRing O] [Fintype ι] [DecidableEq ι] {q : ℕ} (A : Matrix ι (Fin q) O)
    (ρ : Γ →* Matrix ι ι O) (hA : Function.Injective A.mulVec)
    (hst : ∀ g v, ∃ w, A *ᵥ w = ρ g *ᵥ (A *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin q) O, ∀ g, A * (r' g : Matrix (Fin q) (Fin q) O) = ρ g * A := by
  have h1 : ∀ g, ∃ Y : Matrix (Fin q) (Fin q) O, A * Y = ρ g * A := fun g =>
    solve A (ρ g * A) fun j => by
      obtain ⟨w, hw⟩ := hst g (Pi.single j 1)
      refine ⟨w, ?_⟩
      rw [hw, Matrix.mulVec_mulVec]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  choose Y hY using h1
  let f : Γ →* Matrix (Fin q) (Fin q) O :=
    { toFun := Y
      map_one' := cancel_left A hA (by rw [hY, map_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left A hA (by
        rw [hY, map_mul, Matrix.mul_assoc, ← hY h, ← Matrix.mul_assoc, ← hY g, Matrix.mul_assoc]) }
  exact ⟨f.toHomUnits, fun g => by rw [MonoidHom.coe_toHomUnits]; exact hY g⟩

theorem chain_of_lattices : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  intro Γ O _ _ _ _ n t R r ψ ϖ M rs hϖ hM0 hlast hmono hst hline
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hin : ∀ k (y : Fin n → O), (fun a => ϖ * y a) ∈ M k := fun k y =>
    hmono (Fin.zero_le k) ((hM0 _).2 ⟨y, rfl⟩)
  choose A hA hdet using fun k => GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer n ϖ (M k) hϖ0 (hin k)
  have hinj : ∀ k, Function.Injective (A k).mulVec := fun k u v huv => by
    by_contra hne
    refine hdet k ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨u - v, sub_ne_zero.2 hne, ?_⟩)
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hrep : ∀ k, ∃ ρ : Γ →* GL (Fin n) O, Tw ρ r (A k) := fun k =>
    mkRep (A k) ((Units.coeHom _).comp r) (hinj k)
      (fun g v => (hA k _).1 (hst g k _ ((hA k _).2 ⟨v, rfl⟩)))
  choose ρ hρ using hrep
  have hbb : ∀ k : Fin R, ∃ Y, A k.succ * Y = A k.castSucc := fun k =>
    solve _ _ fun j => (hA k.succ _).1 (hmono (Fin.castSucc_lt_succ (i := k)).le
      ((hA k.castSucc _).2 ⟨Pi.single j 1, by funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩))
  choose bb hbbe using hbb
  choose xs hxs hxn hsup hψ using hline
  have hsW : ∀ s w, ∃ u c', A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u + fun a => c' * xs s a := by
    intro s w
    have hm := (hA (rs s).succ _).2 ⟨w, rfl⟩
    rw [hsup s, Submodule.mem_sup] at hm
    obtain ⟨y, hy, z, hz, hyz⟩ := hm
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨u, rfl⟩ := (hA _ _).1 hy
    exact ⟨u, c', by rw [← hyz]; rfl⟩
  have hxW : ∀ s, ∃ w, A (rs s).succ *ᵥ w = xs s := fun s => (hA _ _).1 (hxs s)
  have hcW : ∀ s u, ∃ w, A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u := fun s u =>
    (hA _ _).1 (hmono Fin.castSucc_lt_succ.le ((hA _ _).2 ⟨u, rfl⟩))
  have hnW : ∀ s, ¬ ∃ u, A (rs s).castSucc *ᵥ u = xs s := fun s h => hxn s ((hA _ _).2 h)
  have hψW : ∀ s g, ∃ u, A (rs s).castSucc *ᵥ u =
      (r g : Matrix (Fin n) (Fin n) O) *ᵥ xs s - fun a => ((ψ s g : Oˣ) : O) * xs s a :=
    fun s g => (hA _ _).1 (hψ s g)
  choose r2 B B' C E hL using fun s => GlobalTheory.T.matrix_fibre_product_stable_lattice_chain_line n r (ψ s) (A (rs s).castSucc) (A (rs s).succ) (ρ _) (ρ _)
    (xs s) (hinj _) (hinj _) (hρ _) (hρ _) (hsW s) (hxW s) (hcW s) (hψW s)
  refine ⟨⟨ρ, A, bb, r2, B, B', C, E⟩, fun k => ((A k).map (residue O)).rank,
    ⟨fun k => ⟨hρ k, hdet k, rfl⟩, fun k => ⟨?_, (hbbe k).symm⟩, fun s => hL s⟩, ?_, ?_,
    fun s => GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector n ϖ _ _ (xs s) hϖ (fun y => (hA _ _).1 (hin _ y)) (hsW s) (hxW s) (hcW s) (hnW s)⟩
  · intro g
    apply cancel_left (A k.succ) (hinj _)
    rw [← Matrix.mul_assoc, hbbe k, hρ k.castSucc g, ← hbbe k, ← Matrix.mul_assoc, ← hρ k.succ g,
      Matrix.mul_assoc]
  · have hz : (A 0).map (residue O) = 0 := by
      ext i j
      obtain ⟨y, hy⟩ := (hM0 _).1 ((hA 0 _).2 ⟨Pi.single j 1, rfl⟩)
      have hij : A 0 i j = ϖ * y i := by
        have h1 := congrFun hy i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
      have hr : residue O ϖ = 0 :=
        (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
      simp [hij, hr]
    simp [hz]
  · obtain ⟨S, hS⟩ := solve (A (Fin.last R)) (1 : Matrix (Fin n) (Fin n) O) fun j =>
      (hA _ _).1 (by rw [hlast]; trivial)
    exact (rank_of_mul_eq_one ((A (Fin.last R)).map (residue O)) (S.map (residue O))
      (by rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)])).1

end GlobalTheory.WachChain
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Tors.CoefPull

open GlobalTheory.FieldBaseChange GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.EvalZero

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem cst_map (z : (TF (R := R) F).left) (a : E) :
    cst (R := R) F z (algebraMap E F a) =
      ((baseMap (R := R) E F).left.stalkMap z).hom (cst (R := R) E ((baseMap (R := R) E F).left z) a) := by
  refine Eq.trans ?_ (gs_comp_stalkMap (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _)
  rw [Category.comp_id]
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 _) z ⊤) ?_
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap E F)))

theorem coef_famPull (hf : (algebraMap E F).comp (algebraMap (FractionRing R) E) = algebraMap (FractionRing R) F)
    (hG : GlobalFnsSt) (k : ℕ) (s : Fam D E k) (g : GtPtF D E) (w : Frm D E k g.b)
    (w' : Frm D F k (gtExt D (algebraMap E F) hf g).b) (hw : w.IsGen)
    (hv : ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap E F)) z J) (χ : D.X) :
    coef (famPull D E F hG k s) (gtExt D (algebraMap E F) hf g) w' χ = algebraMap E F (coef s g w χ) := by
  refine coef_eq fun z J hJ => ?_
  let p := baseMap (R := R) E F
  have hJ' : Good D.P.L (p.left z) (fun ψ => J (p.left ≫ ψ)) := fun ψ => hJ (p.left ≫ ψ)
  have a := congrArg (p.left.stalkMap z).hom (isCoef_coef g hw χ s (p.left z) _ hJ')
  rw [map_mul, map_mul, map_mul, map_pow] at a
  have hb : (gtExt D (algebraMap E F) hf g).b = p ≫ g.b := gtExt_b _ hf g
  have e : lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b ≫ famMap D E F = p ≫ lift (𝟙 _) g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, famMap_fst, lift_fst_assoc, Category.assoc, lift_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, lift_snd, ← hb]
      exact (congrArg _ (famMap_snd D E F)).trans (lift_snd _ _)
  have e' : (lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b).left ≫ (famMap D E F).left =
      p.left ≫ (lift (𝟙 _) g.b).left := congrArg (fun q => q.left) e
  refine (congrArg₂ (· * ·) (cst_map z _) (congrArg (· ^ k) ?_)).trans (a.trans
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_).symm)
  · exact val_comp_map (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig p.left
      (TF (R := R) E).hom _ (Over.w p) z hJ
  · refine (sval_pullOver _ _ _ _ hJ).trans ?_
    refine Eq.trans (by rw [e']) ?_
    exact (values_natural _ _ _ _ D.P.L _ _ _ _ p.left z J hJ).2.1 (s.s χ)
  · exact (congrArg Units.val (gtExt_val _ hf g χ hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)
  · exact (congrArg Units.val (hv z J hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)

theorem coef_famPull_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) (k : ℕ) (s : Fam D (FractionRing R) k) (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b) (w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b), w.IsGen → w'.IsGen → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap (FractionRing R) F)) z J) → ∀ χ : D.X, coef (GlobalTheory.FieldBaseChange.famPull D (FractionRing R) F hG k s) (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' χ = algebraMap (FractionRing R) F (coef s g w χ) :=
  fun _ _ _ _ _ _ _ hG k s g w w' hw _ hv χ => coef_famPull _ hG k s g w w' hw hv χ

end GlobalTheory.Poinc.Tors.CoefPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HomFixGerm

open GlobalTheory.AmpleSpan

theorem eq_of_germs {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N)
    (hs : EmbedsBy π s) (f₁ f₂ : X ⟶ Y) (hπ : f₁ ≫ π = f₂ ≫ π)
    (h : ∀ x : X, ∃ σ : κ → X.presheaf.stalk x,
      (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧
      (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) :
    f₁ = f₂ := by
  have mem : ∀ x l, f₁ x ∈ nonzeroLocus (s l) ↔ f₂ x ∈ nonzeroLocus (s l) := by
    intro x l
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    rw [mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁, mem_nonzeroLocus_iff_gs (s l) f₂ x hp₂, e₁ l, e₂ l,
      Units.isUnit_units_mul, Units.isUnit_units_mul]
  have rat : ∀ (l : κ) (r : κ → Γ(Y, nonzeroLocus (s l))), (∀ j, IsRatio (s j) (s l) (r j)) →
      ∀ x j, f₁ x ∈ nonzeroLocus (s l) → gs f₁ x _ (r j) = gs f₂ x _ (r j) := by
    intro l r hr x j hx
    have hx₂ := (mem x l).1 hx
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    have a₁ := (hr j).gs f₁ x hx hp₁
    have a₂ := (hr j).gs f₂ x hx₂ hp₂
    rw [e₁ j, e₁ l] at a₁
    rw [e₂ j, e₂ l] at a₂
    have hσ : IsUnit (σ l) := by
      have := (mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁).1 hx
      rwa [e₁ l, Units.isUnit_units_mul] at this
    have b₁ : σ j = gs f₁ x _ (r j) * σ l := by
      apply u₁.isUnit.mul_left_cancel
      rw [a₁]; ring
    have b₂ : σ j = gs f₂ x _ (r j) * σ l := by
      apply u₂.isUnit.mul_left_cancel
      rw [a₂]; ring
    exact hσ.mul_right_cancel (b₁.symm.trans b₂)
  have loc : ∀ l, (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₁ = (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₂ := by
    intro l
    obtain ⟨haff, r, hr, hsurj⟩ := hs.2 l
    have hV : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ f₂ ⁻¹ᵁ nonzeroLocus (s l) := fun x hx => (mem x l).1 hx
    have happ : f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      have hcomp : (f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) =
          (f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) := by
        refine MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_)
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp, gs_appLE π ⊤ _ le_top f₁ x hx, gs_appLE π ⊤ _ le_top f₂ x (hV hx), hπ]
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp]
          exact rat l r hr x j hx
      ext a
      obtain ⟨P, rfl⟩ := hsurj a
      exact congrArg (fun φ : MvPolynomial κ Γ(Z, ⊤) →+* _ => φ P) hcomp
    haveI : IsAffine (nonzeroLocus (s l)) := haff
    have hres : f₁.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      refine ext_of_isAffine ?_
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happ]
    rw [← Scheme.Hom.resLE_comp_ι f₁ (le_rfl : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ _),
      ← Scheme.Hom.resLE_comp_ι f₂ hV, hres]
  have hcov : TopologicalSpace.IsOpenCover (fun l => f₁ ⁻¹ᵁ nonzeroLocus (s l)) := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show f₁ x ∈ ⨆ l, nonzeroLocus (s l) by rw [hs.1]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hl⟩
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _ hcov) f₁ f₂ fun l => loc l

end GlobalTheory.HomFixGerm
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory

theorem coverUnitary_unimodular :
    ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧
      LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G :=
  fun p q T => ⟨(GlobalTheory.HolDS.haar_unimodular p q T).1, (GlobalTheory.HolDS.haar_unimodular p q T).2,
    GlobalTheory.HolDS.instLocallyCompact T, GlobalTheory.HolDS.instSecondCountable T, GlobalTheory.HolDS.t2Space_cuspAdeles T⟩

end GlobalTheory
end
