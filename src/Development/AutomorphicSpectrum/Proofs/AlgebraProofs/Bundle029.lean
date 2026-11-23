module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle018
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle025
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TensorSpanLe
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.split_characters_unramified : ∀ (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R] [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K), Function.Injective σ → Fintype.card S = Module.finrank ℚ E → ¬ (p : ℤ) ∣ NumberField.discr E → ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧ ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | exact GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit <;> assumption)
end

section

noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubFrob

variable {K : Type} [Field K]

theorem repr_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b : Module.Basis (Fin n) K V)
    (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (x : V) (j : Fin n) :
    b'.repr (F x) j = σ (b.repr x j) := by
  have hx : F x = ∑ k, σ (b.repr x k) • b' k := by
    conv_lhs => rw [← b.sum_repr x]

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, h]
  rw [hx, b'.repr_sum_self]

theorem det_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b c : Module.Basis (Fin n) K V)
    (b' c' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (hc : ∀ j, c' j = F (c j)) :
    b'.det c' = σ (b.det c) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hc]
  exact repr_semilinear F b b' h _ _

theorem isLatOf_spanLat (C : ACurve K) {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ}
    (L : C.I → AddSubgroup V) (i : C.I) (hσ : ∀ a, C.v i a ≤ 1 → C.v i (σ a) ≤ 1)
    (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j))
    (hL : IsLatOf C i b (L i)) : IsLatOf C i b' (spanLat C L F i) := by
  intro y
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, ha, hx, rfl⟩ := hy
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, repr_semilinear F b b' h]
      exact mul_le_one' ha (hσ _ ((hL x).1 hx q))
    | zero => intro q; simp
    | add x y _ _ hx hy =>
      intro q
      rw [map_add (f := _), Finsupp.add_apply]
      exact (C.v i).map_add_le (hx q) (hy q)
    | neg x _ hx =>
      intro q
      rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]
      exact hx q
  · intro hy
    rw [← b'.sum_repr y]
    refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ⟨_, b k, hy k, ?_, by rw [h]⟩
    rw [hL]
    intro q
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isLatOf_comap (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V] (i : C.I)
    {m r : ℕ} (L : AddSubgroup V) (W : Submodule K V) (b : Module.Basis (Fin (m + r)) K V)
    (c : Module.Basis (Fin m) K W) (h : ∀ j, b (Fin.castAdd _ j) = c j) (hL : IsLatOf C i b L) :
    IsLatOf C i c (L.comap W.subtype.toAddMonoidHom) := by
  intro x
  have hx : (x : V) = ∑ k, (Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k) • b k := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, zero_smul, Finset.sum_const_zero, add_zero, h]
    have := congrArg W.subtype (c.sum_repr x)

    rw [map_sum] at this
    exact this.symm
  have hr : ∀ k, b.repr (x : V) k =
      Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k := by
    intro k
    conv_lhs => rw [hx, b.repr_sum_self]
  rw [AddSubgroup.mem_comap]
  change (x : V) ∈ L ↔ _
  rw [hL]
  constructor
  · intro H q
    have := H (Fin.castAdd _ q)
    rwa [hr, Fin.addCases_left] at this
  · intro H q
    rw [hr]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) q
    · rw [Fin.addCases_left]; exact H j
    · rw [Fin.addCases_right]; simp

def mapVec (σ : K →+* K) (d : ℕ) : (Fin d → K) →ₛₗ[σ] (Fin d → K) where
  toFun x := fun j => σ (x j)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem linearIndependent_mapVec (σ : K →+* K) {d n : ℕ} (v : Fin n → Fin d → K)
    (hv : LinearIndependent K v) : LinearIndependent K (fun j => mapVec σ d (v j)) := by
  have h1 : Function.Injective (Matrix.of v).vecMulLinear := by
    have := Matrix.vecMul_injective_iff.2 (show LinearIndependent K (Matrix.of v).row from hv)
    exact this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 h1)
  set B : Matrix (Fin d) (Fin n) K := LinearMap.toMatrixRight' g with hB
  have hgB : ∀ x, g x = Matrix.vecMul x B := by
    intro x
    have : Matrix.toLinearMapRight' B = g := by
      rw [hB]; exact LinearMap.toMatrixRight'.symm_apply_apply g
    rw [← this]; rfl
  have h2 : Matrix.of v * B = 1 := by
    ext a b
    have := congrFun (LinearMap.congr_fun hg (Pi.single a 1)) b
    simp only [LinearMap.comp_apply, hgB, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
      LinearMap.id_apply, Matrix.single_one_vecMul] at this
    rw [Matrix.one_apply]
    change Matrix.vecMul (v a) B b = _
    simpa [Pi.single_apply, eq_comm] using this
  have h3 : (Matrix.of v).map σ * B.map σ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ σ.map_zero σ.map_one]
  have h4 : LinearIndependent K ((Matrix.of v).map σ).row := by
    rw [← Matrix.vecMul_injective_iff]
    intro x y hxy
    have := congrArg (fun z => Matrix.vecMul z (B.map σ)) hxy
    simpa [Matrix.vecMul_vecMul, h3] using this
  exact h4

theorem exists_basis_top (σ : K →+* K) {d n : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ j, b' j = mapVec σ d (b j) :=
  ⟨basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_mapVec σ b b.linearIndependent)
    (Module.finrank_eq_card_basis b).symm, fun j => by simp⟩

theorem exists_basis_sub (σ : K →+* K) {d n : ℕ} (W : Submodule K (Fin d → K))
    (c : Module.Basis (Fin n) K W) :
    ∃ c' : Module.Basis (Fin n) K (Submodule.span K (mapVec σ d '' (W : Set (Fin d → K)))),
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
  have hli := linearIndependent_mapVec σ (fun j => (c j : Fin d → K))
    (c.linearIndependent.map' W.subtype W.ker_subtype)
  have hs : Submodule.span K (Set.range fun j => mapVec σ d (c j)) =
      Submodule.span K (mapVec σ d '' (W : Set (Fin d → K))) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨c j, (c j).2, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have : x = ∑ k, c.repr ⟨x, hx⟩ k • (c k : Fin d → K) := by
        have := congrArg W.subtype (c.sum_repr ⟨x, hx⟩)

        rw [map_sum] at this
        exact this.symm

      rw [this, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs), fun j => ?_⟩
  simp [Module.Basis.span_apply]

theorem subDeg_frob : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W : Submodule K (Fin d → K)), IsBun C L → subDeg C (frobLat C p L) (frobSub p W) = p * subDeg C L W := by
  intro K _ C p _ _ d L W hL
  set σ := frobenius K p with hσ
  have hL' : IsBun C (frobLat C p L) := (GlobalTheory.T.frobenius_lattice_degree_mul_p K C p d L hL).1
  have hS := (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1
  have hS' := (GlobalTheory.T.sub_and_quotient_bundles K C _ _ (frobSub p W) hL').1
  have hv : ∀ i a, C.v i (σ a) = C.v i a ^ p := fun i a => by rw [hσ, frobenius_def, map_pow]
  have key : ∀ i, ∃ (c : Module.Basis (Fin (Module.finrank K W)) K W)
      (c' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W)),
      IsLatOf C i c (sub C L W i) ∧ IsLatOf C i c' (sub C (frobLat C p L) (frobSub p W) i) ∧
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
    intro i
    obtain ⟨b, hb⟩ := hL.1 i
    obtain ⟨c, -, b₁, hb₁, hc, -, hbc, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C _ i _ b (L i) W hb
    obtain ⟨b', hb'⟩ := exists_basis_top σ b₁
    obtain ⟨c', hc'⟩ := exists_basis_sub σ W c
    refine ⟨c, c', hc, ?_, hc'⟩
    refine isLatOf_comap C i _ _ b' c' (fun j => by rw [hb', hbc]; exact (hc' j).symm) ?_
    exact isLatOf_spanLat C (mapVec σ d) L i (fun a ha => by rw [hv]; exact pow_le_one' ha p)
      b₁ b' hb' hb₁
  choose c c' hc hc' hcc using key
  obtain ⟨e', he'⟩ : ∃ e' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W),
      ∀ j, (e' j : Fin d → K) = mapVec σ d (Module.finBasis K W j) :=
    exists_basis_sub σ W (Module.finBasis K W)
  let G : W →ₛₗ[σ] frobSub p W :=
    ((mapVec σ d).domRestrict W).codRestrict (frobSub p W)
      (fun x => Submodule.subset_span ⟨x, x.2, rfl⟩)
  obtain ⟨-, h1⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ (Module.finBasis K W) c hS hc
  obtain ⟨-, h2⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ e' c' hS' hc'
  unfold subDeg
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  have hd := det_semilinear G (Module.finBasis K W) (c i) e' (c' i)
    (fun j => Subtype.ext (he' j)) (fun j => Subtype.ext (hcc i j))
  rw [hd, hv, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.SubFrob
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.generation_along_invariants : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | exact GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.augmentation_lengths_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∃ cA cN cO : NNReal, cA ≠ 0 ∧ cN ≠ 0 ∧ cO ≠ 0 ∧ HasLen v R (AFQuot p AA.carrier) cA ∧ HasColen R v AA.carrier cN ∧ HasLen v R (OmAA AA.carrier) cO := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.lens_exist | exact GlobalTheory.CompanionTheory.Ar.GR.lens_exist | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.lens_exist <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.augmentation_quotient_equiv_lattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | exact GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  first | exact @PositivityTheory.HtPt.Rh.sub_closed | exact PositivityTheory.HtPt.Rh.sub_closed
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem apply_of_mem_eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {x : V}
    (hx : x ∈ eigSp ρ σ) (a : 𝓞 E) : ρ a x = σ (a : E) • x := by
  have := (Submodule.mem_iInf _).1 hx a
  simpa [sub_eq_zero] using this

theorem sum_smul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {N : ℕ} (t : Fin N → V)
    (y : Fin N → K) :
    ∑ i, y i • eigProj ρ σ (t i) =
      ∑ q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E),
        (y q.1 * σ (dualInt E q.2)) • ρ (RingOfIntegers.basis E q.2) (t q.1) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eigProj, LinearMap.sum_apply, Finset.smul_sum, mul_smul]

omit [Algebra A K] [IsScalarTower A K V] in
theorem mem_of_isFreeOn (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) {N : ℕ} (t : Fin N → V)
    (h : IsFreeOn ρ X t) (i : Fin N) : t i ∈ X := by
  have h1 : t i = ∑ k, (RingOfIntegers.basis E).repr 1 k • ρ (RingOfIntegers.basis E k) (t i) := by
    have := congrArg (fun a => ρ a (t i)) ((RingOfIntegers.basis E).sum_repr 1)

    simp only [map_sum, map_zsmul, map_one, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.one_apply] at this
    exact this.symm
  rw [h1, h.2.2]
  refine Submodule.sum_mem _ fun k _ => ?_
  refine zsmul_mem ?_ _
  exact Submodule.subset_span ⟨(i, k), rfl⟩

theorem eigSub_eq_different_smul_eigQuot : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) (N : ℕ) (t : Fin N → V) (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → IsFreeOn ρ X t → (∀ x, x ∈ eigQuot ρ σ X ↔ d • x ∈ eigSub ρ σ X) ∧ eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) ∧ LinearIndependent K (fun i => eigProj ρ σ (t i)) ∧ Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
  intro A K _ _ _ _ V _ _ _ _ E _ _ ρ X N t σ d hinj hσ hd hX
  obtain ⟨he1, he2, -, he4⟩ := ProjEig.eigProj_spec K V E ρ σ
  obtain ⟨hd0, hd1, u, hu⟩ := GlobalTheory.T.different_generator_dual_integral A K E σ d hinj hσ hd
  have hQ : eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) := by
    apply le_antisymm
    · unfold eigQuot
      rw [hX.2.2, Submodule.map_span_le]
      rintro _ ⟨⟨i, k⟩, rfl⟩
      obtain ⟨a, ha⟩ := hσ (RingOfIntegers.basis E k)
      have : eigProj ρ σ (ρ (RingOfIntegers.basis E k) (t i)) = a • eigProj ρ σ (t i) := by
        rw [← Module.End.mul_apply, he4, Module.End.mul_apply,
          apply_of_mem_eigSp ρ σ (he1 _), ← ha, IsScalarTower.algebraMap_smul]
      simp only [LinearMap.restrictScalars_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨t i, mem_of_isFreeOn ρ X t hX i, rfl⟩
  have hli : LinearIndependent K (fun i => eigProj ρ σ (t i)) := by
    rw [Fintype.linearIndependent_iff]
    intro y hy i
    rw [sum_smul_eigProj] at hy
    have h0 := Fintype.linearIndependent_iff.1 hX.1 _ hy
    calc y i = y i * ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) := by
          rw [hu, mul_one]
      _ = ∑ k, algebraMap A K (u k) * algebraMap A K d * (y i * σ (dualInt E k)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          have := h0 (i, k)
          simp only at this
          rw [this, mul_zero]
  have hsp : Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact he1 _
    · intro x hx
      rw [← he2 x hx]
      have hx' : x ∈ Submodule.span K (X : Set V) := by rw [hX.2.1]; trivial
      have : (Submodule.span K (X : Set V)).map (eigProj ρ σ) ≤
          Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) := by
        rw [Submodule.map_span_le]
        intro m hm
        apply Submodule.span_le_restrictScalars A K
        rw [← hQ]
        exact ⟨m, hm, rfl⟩
      exact this ⟨x, hx', rfl⟩
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hQ, hli, hsp⟩
  · refine ⟨?_, ?_⟩
    · rw [hQ, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, rfl⟩ := hx
      have : d • ∑ i, c i • eigProj ρ σ (t i) =
          ∑ i, (algebraMap A K (c i) * algebraMap A K d) • eigProj ρ σ (t i) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_mul, IsScalarTower.algebraMap_smul, mul_comm, mul_smul]
      rw [this, sum_smul_eigProj, hX.2.2]
      refine Submodule.sum_mem _ fun q _ => ?_
      obtain ⟨a, ha⟩ := hd1 q.2
      rw [mul_assoc, ← ha, ← map_mul, IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    · obtain ⟨m, -, rfl⟩ := hx
      exact Submodule.smul_mem _ d (show _ ∈ (eigSp ρ σ).restrictScalars A from he1 m)
  · obtain ⟨hx1, hx2⟩ := hx
    have hxe : x ∈ eigSp ρ σ := by
      have h2 : algebraMap A K d • x ∈ eigSp ρ σ := by
        rw [IsScalarTower.algebraMap_smul]; exact hx2
      exact (Submodule.smul_mem_iff _ hd0).1 h2
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hxe
    obtain ⟨y, rfl⟩ := hxe
    have hx1' : d • ∑ i, y i • eigProj ρ σ (t i) ∈ X := hx1
    rw [hX.2.2, Submodule.mem_span_range_iff_exists_fun] at hx1'
    obtain ⟨c, hc⟩ := hx1'
    have h3 : d • ∑ i, y i • eigProj ρ σ (t i) =
        ∑ i, (y i * algebraMap A K d) • eigProj ρ σ (t i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul, IsScalarTower.algebraMap_smul]
    rw [h3, sum_smul_eigProj] at hc
    have h4 : ∀ q, algebraMap A K (c q) = y q.1 * algebraMap A K d * σ (dualInt E q.2) := by
      refine Fintype.linearIndependent_iffₛ.1 hX.1 _ _ ?_
      rw [← hc]
      exact Finset.sum_congr rfl fun q _ => IsScalarTower.algebraMap_smul _ _ _
    rw [hQ]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h5 : y i = algebraMap A K (∑ k, u k * c (i, k)) := by

      rw [map_sum, ← mul_one (y i), ← hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, h4]
      ring
    rw [h5, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.character_ideal_principal_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ AA _ χ
  obtain ⟨B, hB, hM⟩ := AA.lat
  have key : ∀ d : R, d ∈ xIdeal AA.carrier χ ↔
      (d • fun a => algebraMap R C (χ a)) ∈ AA.carrier := fun d => by
    simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have smul_char (c : R) :
      (c • fun a => algebraMap R C (χ a)) = fun a => algebraMap R C (c * χ a) := by
    funext a
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_denominator v hv (B⁻¹ *ᵥ fun a => algebraMap R C (χ a))
    refine ⟨c, hc0, ?_⟩
    ext d
    rw [key, hM, mem_span_cols_iff B hB, ← hc d]
    refine forall_congr' fun j => exists_congr fun r => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  · intro g
    constructor
    · rintro ⟨hgM, hg⟩
      have hint : ∀ x, ∃ r : R, algebraMap R C r = g x := AA.le_int hgM
      obtain ⟨r, hr⟩ := hint 1
      have hgf : g = fun a => algebraMap R C (r * χ a) := by
        funext a
        have h := hg a 1
        rw [smul_eq_mul, mul_one] at h
        rw [h, ← hr, map_mul]
        exact mul_comm _ _
      refine ⟨r, ?_, hgf⟩
      rw [key, smul_char, ← hgf]
      exact hgM
    · rintro ⟨c, hc, rfl⟩
      rw [key, smul_char] at hc
      refine ⟨hc, fun a x => ?_⟩
      simp only [smul_eq_mul, map_mul]
      ring
end
