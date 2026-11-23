module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_stable_lattice {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A)
    (hd : d ≠ 0) (h : ∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) :
    ∃ L : Submodule A (Fin m → F), Submodule.IsFullLattice F L ∧
      ∀ g, ∀ x ∈ L, (r g : Matrix (Fin m) (Fin m) F) *ᵥ x ∈ L := by
  classical
  let S : Set (Fin m → F) :=
    Set.range fun p : G × Fin m => (r p.1 : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single p.2 1)
  have hd' : algebraMap A F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
  refine ⟨Submodule.span A S,
    { toIsLattice := Submodule.IsLattice.of_fg F ?_, span_eq_top := ?_ }, ?_⟩
  · let N : Submodule A (Fin m → F) :=
      Submodule.span A (Set.range fun i : Fin m => (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F))
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine hN.of_le ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, j⟩, rfl⟩
    choose a ha using h g
    have e : (r g : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single j 1) =
        ∑ i, a i j • (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F) := by
      funext k
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Algebra.smul_def, ← ha]
      field_simp
    simp only [SetLike.mem_coe]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff, ← (Pi.basisFun F (Fin m)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by
      simp only [map_one, Units.val_one, Matrix.one_mulVec, Pi.basisFun_apply]⟩
  · intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g', i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * g', i), by
        simp only [map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

theorem UpperTheory.V.Pa.Det.latInt :
    ∀ {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A), d ≠ 0 → (∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) → ∃ (Q : GL (Fin m) F) (r₀ : G →* GL (Fin m) A), ∀ g, r g * Q = Q * pushRep (algebraMap A F) r₀ g := by
  intro A F G _ _ _ _ _ _ _ m r d hd h
  classical
  obtain ⟨L, hL, hst⟩ := exists_stable_lattice r d hd h
  have hr : Module.finrank A L = m := by
    simpa using ((Submodule.IsFullLattice.finrank_eq F L).trans (Module.finrank_fintype_fun_eq_card F))
  have := Submodule.IsLattice.free F L
  have := Submodule.IsLattice.finite F L
  let bL : Module.Basis (Fin m) A L := Module.finBasisOfFinrankEq A L hr
  let b : Module.Basis (Fin m) F (Fin m → F) := bL.extendOfIsFullLattice F
  let Q₀ : Matrix (Fin m) (Fin m) F := (Pi.basisFun F (Fin m)).toMatrix b
  have hQ : IsUnit Q₀ := by
    letI := (Pi.basisFun F (Fin m)).invertibleToMatrix b
    exact isUnit_of_invertible _
  have hQa : ∀ i j, Q₀ i j = (bL j : Fin m → F) i := fun i j => by
    simp [Q₀, b, Module.Basis.toMatrix_apply]
  let M : G → Matrix (Fin m) (Fin m) A := fun g k j => bL.repr ⟨_, hst g _ (bL j).2⟩ k
  have hM : ∀ g, (r g : Matrix (Fin m) (Fin m) F) * Q₀ = Q₀ * (M g).map (algebraMap A F) := by
    intro g
    ext i j
    have e := congrArg (fun x : L => (x : Fin m → F) i) (bL.sum_repr ⟨_, hst g _ (bL j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Algebra.smul_def] at e
    simp only [Matrix.mul_apply, hQa, Matrix.map_apply]
    refine Eq.trans e.symm ?_
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have inj : ∀ X Y : Matrix (Fin m) (Fin m) A,
      Q₀ * X.map (algebraMap A F) = Q₀ * Y.map (algebraMap A F) → X = Y := fun X Y hXY =>
    Matrix.map_injective (IsFractionRing.injective A F) (hQ.mul_left_cancel hXY)
  let M' : G →* Matrix (Fin m) (Fin m) A :=
    { toFun := M
      map_one' := inj _ _ (by rw [← hM]; simp)
      map_mul' := fun g g' => inj _ _ (by
        rw [← hM, Matrix.map_mul, ← mul_assoc, ← hM, mul_assoc, ← hM, map_mul, Units.val_mul,
          mul_assoc]) }
  refine ⟨hQ.unit, M'.toHomUnits, fun g => Units.ext ?_⟩
  exact hM g
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.solBase :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ} (e : ι → F) (r : ι → Matrix (Fin n) (Fin n) F), (∀ X : Matrix (Fin n) (Fin n) F, (∀ i, e i • (r i * X) = X * r i) → X = 0) → ∀ X : Matrix (Fin n) (Fin n) F', (∀ i, f (e i) • ((r i).map f * X) = X * (r i).map f) → X = 0 := by
  intro F F' ι _ _ f n e r h X hX
  letI : Algebra F F' := f.toAlgebra
  have hs : ∀ (x : F) (y : F'), f x * y = x • y := fun x y => (Algebra.smul_def x y).symm
  let b := Module.Basis.ofVectorSpace F F'
  have key : ∀ k, (Matrix.of fun a c => b.repr (X a c) k) = 0 := by
    intro k
    apply h
    intro i
    ext a c
    have hac := congrArg (fun M => b.repr (M a c) k) (hX i)
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Matrix.of_apply] at hac ⊢

    simp only [hs, mul_comm (X _ _) (f _), ← Finset.smul_sum, map_sum, map_smul, Finsupp.smul_apply,
    smul_eq_mul] at hac
    change e i * (Finsupp.applyAddHom k : (_ →₀ F) →+ F) (∑ x, r i a x • b.repr (X x c)) =
      (Finsupp.applyAddHom k : (_ →₀ F) →+ F) (∑ x, r i x c • b.repr (X a x)) at hac
    simp only [map_sum, Finsupp.applyAddHom_apply, Finsupp.smul_apply, smul_eq_mul] at hac
    simpa only [mul_comm] using hac
  ext a c
  have hk : b.repr (X a c) = 0 := by
    ext k
    exact congrFun (congrFun (key k) a) c
  simpa using hk
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.exists_integral_block_iwasawa_decomposition :
    ∀ {A F : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] {n : ℕ} (bl ty : Fin n → Bool) (g : GL (Fin n) F), (∀ i j, bl i ≠ ty j → g i j = 0) → ∃ (w : GL (Fin n) A) (b : GL (Fin n) F), (∀ i j, j < i → b i j = 0) ∧ GeneralLinearGroup.map (algebraMap A F) w = g * b ∧ ∀ i j, bl i ≠ ty j → w i j = 0 := by
  intro A F _ _ _ _ _ _ n bl ty g hg
  obtain ⟨k, b0, hb0, hgkb⟩ := GlobalTheory.ValIwasawa.iwasawa A F n g
  haveI : Invertible (b0 : Matrix (Fin n) (Fin n) F) := Units.invertible b0
  have hctri : ((b0 : Matrix (Fin n) (Fin n) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular hb0
  set c : Matrix (Fin n) (Fin n) F := (b0 : Matrix (Fin n) (Fin n) F)⁻¹ with hcdef
  have hgc : (g : Matrix (Fin n) (Fin n) F) * c = (GeneralLinearGroup.map (algebraMap A F) k : Matrix (Fin n) (Fin n) F) := by
    have h1 : g * b0⁻¹ = GeneralLinearGroup.map (algebraMap A F) k := mul_inv_eq_iff_eq_mul.mpr hgkb
    have h2 := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1
    simpa [Units.val_mul, Matrix.coe_units_inv, hcdef] using h2
  let c' : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => if ty i = ty j then c i j else 0
  have hc'tri : c'.BlockTriangular id := by
    intro i j hij
    simp only [c', Matrix.of_apply]
    split_ifs
    · exact hctri hij
    · rfl
  have hgc' : ∀ i j, ((g : Matrix (Fin n) (Fin n) F) * c') i j = if bl i = ty j then algebraMap A F ((k : Matrix (Fin n) (Fin n) A) i j) else 0 := by
    intro i j
    rw [Matrix.mul_apply]
    split_ifs with hij
    · rw [← GeneralLinearGroup.map_apply, ← hgc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rfl
      · rw [hg i l (fun h => hl (h.symm.trans hij)), zero_mul, zero_mul]
    · refine Finset.sum_eq_zero fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rw [hg i l (fun h => hij (h.trans hl)), zero_mul]
      · rw [mul_zero]
  let kw : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => if bl i = ty j then (k : Matrix (Fin n) (Fin n) A) i j else 0
  have hmap : (algebraMap A F).mapMatrix kw = (g : Matrix (Fin n) (Fin n) F) * c' := by
    ext i j
    rw [hgc' i j]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, kw, Matrix.of_apply]
    split_ifs
    · rfl
    · exact map_zero _
  have hdetc : c'.det = c.det := by
    rw [Matrix.det_of_upperTriangular hc'tri, Matrix.det_of_upperTriangular hctri]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [c']
  have hcunit : IsUnit c.det := by
    have := Matrix.isUnits_det_units b0⁻¹
    rwa [Matrix.coe_units_inv] at this
  have hc'unit : IsUnit c'.det := hdetc ▸ hcunit
  have hdetk : kw.det = (k : Matrix (Fin n) (Fin n) A).det := by
    apply IsFractionRing.injective A F
    rw [RingHom.map_det, RingHom.map_det, hmap, Matrix.det_mul, hdetc, ← Matrix.det_mul, hgc]
    rfl
  have hkunit : IsUnit kw.det := hdetk ▸ Matrix.isUnits_det_units k
  refine ⟨GeneralLinearGroup.mk'' kw hkunit, GeneralLinearGroup.mk'' c' hc'unit, ?_, ?_, ?_⟩
  · intro i j hij
    exact hc'tri hij
  · apply Units.ext
    rw [Units.val_mul]
    exact hmap
  · intro i j hij
    show kw i j = 0
    simp [kw, hij]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.finSub :
    ∀ {A M ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M] (t : A) (Z B : Submodule A M) (f : ι → M →ₗ[A] A), Irreducible t → Z.FG → (∀ i, ∀ b ∈ B, f i b = 0) → (∀ z ∈ Z, (∀ i, f i z = 0) → ∃ s : ℕ, t ^ s • z ∈ B) → ∃ T : Finset ι, ∀ z ∈ Z, (∀ i ∈ T, f i z = 0) → ∃ s : ℕ, t ^ s • z ∈ B := by
  intro A M ι _ _ _ _ _ t Z B f ht hZ hB hZB
  classical
  obtain ⟨s, rfl⟩ := hZ
  let h : ι → (↥s → A) := fun i a => f i a.1
  obtain ⟨P, ⟨T, rfl⟩, hP⟩ := (set_has_maximal_iff_noetherian (R := A) (M := ↥s → A)).mpr
    inferInstance (Set.range fun T : Finset ι => Submodule.span A (h '' (T : Set ι))) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨T, fun z hz hzT => hZB z hz fun j => ?_⟩
  have hj : h j ∈ Submodule.span A (h '' (T : Set ι)) := by
    have hle : Submodule.span A (h '' (T : Set ι)) ≤
        Submodule.span A (h '' ((insert j T : Finset ι) : Set ι)) :=
      Submodule.span_mono (Set.image_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
    have heq := (eq_or_lt_of_le hle).resolve_right (hP _ ⟨insert j T, rfl⟩)
    rw [heq]
    exact Submodule.subset_span ⟨j, by simp, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_finset'.mp hz
  let E : (↥s → A) →ₗ[A] A := Fintype.linearCombination A c
  have hE : ∀ i, f i (∑ a : ↥s, c a • a.1) = E (h i) := by
    intro i

    simp [E, h, Fintype.linearCombination_apply, map_sum, mul_comm]
  have hker : Submodule.span A (h '' (T : Set ι)) ≤ LinearMap.ker E := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [← hE]
    exact hzT i hi
  rw [hE]
  exact hker hj
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.maxIndep :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M] (t : A) (S B : Submodule A M), Irreducible t → S.FG → ∃ (g : ℕ) (κ : Fin g → M), (∀ j, κ j ∈ S) ∧ (∀ c : Fin g → A, ∑ j, c j • κ j ∈ B → c = 0) ∧ ∀ z ∈ S, ∃ (s : ℕ) (c : Fin g → A), t ^ s • z - ∑ j, c j • κ j ∈ B := by
  intro A M _ _ _ _ _ t S B ht hS
  haveI : Module.Finite A (S.map B.mkQ) := Module.Finite.iff_fg.mpr (hS.map _)
  obtain ⟨n, ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_free_prod_directSum A (S.map B.mkQ)
  let ψ : (Fin n →₀ A) →ₗ[A] S.map B.mkQ := φ.symm.toLinearMap ∘ₗ LinearMap.inl A _ _
  have hlift : ∀ j : Fin n, ∃ m ∈ S, B.mkQ m = (ψ (Finsupp.single j 1) : M ⧸ B) :=
    fun j => Submodule.mem_map.mp (ψ (Finsupp.single j 1)).2
  choose κ hκS hκ using hlift
  have hψinj : Function.Injective ψ := φ.symm.injective.comp LinearMap.inl_injective
  have hli : LinearIndependent A (fun j => (ψ (Finsupp.single j 1) : M ⧸ B)) := by
    have h1 := (Finsupp.basisSingleOne (R := A) (ι := Fin n)).linearIndependent
    have h2 := h1.map' ψ (LinearMap.ker_eq_bot.mpr hψinj)
    have h3 := h2.map' (S.map B.mkQ).subtype (Submodule.ker_subtype _)
    simpa [Function.comp_def] using h3
  refine ⟨n, κ, hκS, ?_, ?_⟩
  · intro c hc
    have h0 : ∑ j, c j • (ψ (Finsupp.single j 1) : M ⧸ B) = 0 := by

      simp_rw [← hκ, ← map_smul, ← map_sum]
      exact (Submodule.Quotient.mk_eq_zero B).mpr hc
    funext j
    exact Fintype.linearIndependent_iff.mp hli c h0 j
  · intro z hz
    let w : S.map B.mkQ := ⟨B.mkQ z, Submodule.mem_map_of_mem hz⟩
    let K := ∑ i, e i
    have hd : t ^ K • (φ w).2 = 0 := by
      refine DFinsupp.ext fun i => ?_
      rw [DirectSum.smul_apply, DirectSum.zero_apply]
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ ((φ w).2 i)
      rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
      obtain ⟨u, hu⟩ := ((IsDiscreteValuationRing.associated_of_irreducible A (hp i) ht).pow_pow (n := e i)).dvd.trans
        (pow_dvd_pow t (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
      exact ⟨u * x, by rw [hu, smul_eq_mul, smul_eq_mul]; ring⟩
    have hφ : t ^ K • w = ψ (t ^ K • (φ w).1) := by
      apply φ.injective
      rw [map_smul]
      show t ^ K • φ w = φ (φ.symm (t ^ K • (φ w).1, 0))
      rw [LinearEquiv.apply_symm_apply]
      ext1
      · rfl
      · exact hd
    refine ⟨K, fun j => t ^ K * (φ w).1 j, ?_⟩

    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, map_sum]
    simp_rw [map_smul, hκ]
    have hz' : B.mkQ z = (w : M ⧸ B) := rfl
    rw [hz', sub_eq_zero, ← Submodule.coe_smul, hφ]
    conv_lhs => rw [← Finsupp.univ_sum_single (t ^ K • (φ w).1)]

    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, ← Finsupp.smul_single_one, map_smul, Submodule.coe_smul]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.sqExt :
    ∀ {K : Type} [Field K], ∃ j : PowerSeries K →+* PowerSeries K, Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ j PowerSeries.X = PowerSeries.X ^ 2 := by
  intro K _
  refine ⟨(PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom, ?_, ?_, ?_, by simp⟩
  · intro f g h
    ext m
    have h1 := congrArg (PowerSeries.coeff (2 * m)) h
    simpa using h1
  · refine ⟨fun f hf => ?_⟩
    rw [PowerSeries.isUnit_iff_constantCoeff] at hf ⊢
    simpa using hf
  · classical
    letI inst : Module (PowerSeries K) (PowerSeries K) :=
      (PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom.toAlgebra.toModule
    have hs : Submodule.span (PowerSeries K) ({1, PowerSeries.X} : Set (PowerSeries K)) = ⊤ := by
      rw [eq_top_iff]
      intro f _
      rw [Submodule.mem_span_pair]
      refine ⟨PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f,
        PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f, ?_⟩
      change PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f) * 1 +
        PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f) *
          PowerSeries.X = f
      ext n
      rw [mul_one, map_add (f := _), ← pow_one (PowerSeries.X (R := K)), PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      simp only [PowerSeries.coeff_mk]
      split_ifs <;> first | omega | (simp only [add_zero, zero_add]; congr; omega)
    exact ⟨⟨{1, PowerSeries.X}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact hs⟩⟩
end
