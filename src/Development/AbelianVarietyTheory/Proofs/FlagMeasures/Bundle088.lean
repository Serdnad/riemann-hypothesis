module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.UnitriHaar

theorem map_add_nilpotent {k G : Type*} [NormedField k] [IsUltrametricDist k] [ProperSpace k]
    [AddCommGroup G] [Module k G] [Module.Finite k G] [TopologicalSpace G] [IsModuleTopology k G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (N : Module.End k G) (hN : IsNilpotent N) : μ.map (fun x => x + N x) = μ := by
  have : IsTopologicalAddGroup G := IsModuleTopology.topologicalAddGroup k G
  let e₀ : G ≃ₗ[k] (Fin (Module.finrank k G) → k) := (Module.finBasis k G).equivFun
  let e : G ≃ₜ (Fin (Module.finrank k G) → k) :=
    { e₀.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap }
  have : LocallyCompactSpace G := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology G := e.secondCountableTopology
  have hc : ∀ f : Module.End k G, Continuous f := fun f => IsModuleTopology.continuous_of_linearMap f
  let K₀ := IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank k G) → k) one_pos
  let K : AddSubgroup G := K₀.toAddSubgroup.comap e₀.toLinearMap.toAddMonoidHom
  have hKo : IsOpen (K : Set G) := K₀.isOpen.preimage e.continuous
  have hKc : IsCompact (K : Set G) :=
    e.isCompact_preimage.2 (isCompact_closedBall (0 : Fin (Module.finrank k G) → k) 1)
  obtain ⟨m, hm⟩ := hN
  let B : AddSubgroup G := ⨅ j : ℕ, K.comap (N ^ j).toAddMonoidHom
  have hB : ∀ x, x ∈ B ↔ ∀ j : ℕ, (N ^ j) x ∈ K := fun x => by
    simp [B, AddSubgroup.mem_iInf]
  have hBo : IsOpen (B : Set G) := by
    have : (B : Set G) = ⋂ j ∈ Finset.range m, (N ^ j : Module.End k G) ⁻¹' (K : Set G) := by
      ext x
      simp only [SetLike.mem_coe, hB, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      refine ⟨fun h j _ => h j, fun h j => ?_⟩
      by_cases hj : j < m
      · exact h j hj
      · rw [pow_eq_zero_of_le (not_lt.1 hj) hm]; exact K.zero_mem
    rw [this]
    exact isOpen_biInter_finset fun j _ => hKo.preimage (hc _)
  have hBc : IsCompact (B : Set G) :=
    hKc.of_isClosed_subset (B.isClosed_of_isOpen hBo) fun x hx => by
      simpa using (hB x).1 hx 0
  have hNB : ∀ x ∈ B, N x ∈ B := fun x hx => (hB _).2 fun j => by
    rw [← Module.End.mul_apply, ← pow_succ]; exact (hB x).1 hx _
  have hNp : ∀ (j : ℕ), ∀ x ∈ B, ((-N) ^ j) x ∈ B := fun j => by
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact B.neg_mem (hNB _ (ih x hx))
  have hm' : (-N) ^ m = 0 := by rw [neg_pow, hm, mul_zero]
  have h1 : (∑ j ∈ Finset.range m, (-N) ^ j) * (1 + N) = 1 := by
    have := geom_sum_mul_neg (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have h2 : (1 + N) * (∑ j ∈ Finset.range m, (-N) ^ j) = 1 := by
    have := mul_neg_geom_sum (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  let L : G ≃ₜ+ G :=
    { toFun := fun x => x + N x
      invFun := (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G)
      left_inv := fun x => LinearMap.congr_fun h1 x
      right_inv := fun x => LinearMap.congr_fun h2 x
      map_add' := fun x y => by rw [map_add (f := _)]; abel
      continuous_toFun := continuous_id.add (hc N)
      continuous_invFun := hc _ }
  have hLB : L ⁻¹' (B : Set G) = B := by
    ext x
    refine ⟨fun hx => ?_, fun hx => B.add_mem hx (hNB x hx)⟩
    have : x = (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G) (L x) := (L.left_inv x).symm
    rw [this, LinearMap.sum_apply]
    exact B.sum_mem fun j _ => hNp j _ hx
  change μ.map L = μ
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have h3 := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  have h4 : μ.map L B = μ B := by
    rw [Measure.map_apply (show Continuous L from L.continuous).measurable hBo.measurableSet, hLB]
  have h5 : μ B ≠ 0 := (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne'
  have h6 : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have h7 : Measure.addHaarScalarFactor (μ.map L) μ = 1 := by
    rw [h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
    have := (ENNReal.mul_left_inj h5 h6).1 (h4.trans (one_mul _).symm)
    exact_mod_cast this
  rw [h3, h7, one_smul]

theorem nilpotent_of_strict {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ a b, ¬ a < b → A a b = 0) : A ^ n = 0 := by
  have : ∀ (j : ℕ) (a b : Fin n), b.val < a.val + j → (A ^ j) a b = 0 := fun j => by
    induction j with
    | zero => intro a b h; rw [pow_zero, Matrix.one_apply_ne]; rintro rfl; omega
    | succ j ih =>
      intro a b h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c < b
      · rw [ih a c (by have : c.val < b.val := hc; omega), zero_mul]
      · rw [hA c b hc, mul_zero]
  exact Matrix.ext fun a b => this n a b (by omega)

def strictOf (R : Type*) [CommRing R] (n : ℕ) :
    ({p : Fin n × Fin n // p.1 < p.2} → R) →ₗ[R] Matrix (Fin n) (Fin n) R where
  toFun x := Matrix.of fun a b => if h : a < b then x ⟨(a, b), h⟩ else 0
  map_add' x y := by ext a b; simp only [Matrix.add_apply, Matrix.of_apply]; split_ifs <;> simp
  map_smul' c x := by ext a b; simp only [Matrix.smul_apply, Matrix.of_apply]; split_ifs <;> simp

def above (R : Type*) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →ₗ[R] ({p : Fin n × Fin n // p.1 < p.2} → R) where
  toFun A p := A p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_nilpotent {R : Type*} [CommRing R] {n : ℕ} (u : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ i, u i i = 1) (h0 : ∀ i j, j < i → u i j = 0) :
    ∃ N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R), IsNilpotent N ∧
      ∀ x : {p : Fin n × Fin n // p.1 < p.2} → R,
        (fun p : {p : Fin n × Fin n // p.1 < p.2} => (u * Matrix.of (fun a b : Fin n =>
          (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R))) p.1.1 p.1.2) =
        above R n u + (x + N x) := by
  have hu : ∀ a b, ¬ a < b → (u - 1) a b = 0 := fun a b h => by
    rcases (not_lt.1 h).eq_or_lt with rfl | h
    · simp [h1]
    · simp [h0 a b h, Matrix.one_apply_ne h.ne']
  have hs : ∀ x a b, ¬ a < b → strictOf R n x a b = 0 := fun x a b h => dif_neg h
  have has : ∀ x, above R n (strictOf R n x) = x := fun x => funext fun p => dif_pos p.2
  let N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    above R n ∘ₗ LinearMap.mulLeft R (u - 1) ∘ₗ strictOf R n
  have hN : ∀ x, strictOf R n (N x) = (u - 1) * strictOf R n x := fun x => by
    ext a b
    by_cases h : a < b
    · exact dif_pos h
    · rw [hs _ a b h, Matrix.mul_apply]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      by_cases hc : a < c
      · rw [hs x c b fun h' => h (hc.trans h'), mul_zero]
      · rw [hu a c hc, zero_mul]
  have hp : ∀ (j : ℕ) x, strictOf R n ((N ^ j) x) = (u - 1) ^ j * strictOf R n x := fun j => by
    induction j with
    | zero => simp
    | succ j ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, hN, ih, mul_assoc]
  refine ⟨N, ⟨n, LinearMap.ext fun x => ?_⟩, fun x => ?_⟩
  · rw [← has ((N ^ n) x), hp, nilpotent_of_strict _ hu, zero_mul, map_zero, LinearMap.zero_apply]
  · have : Matrix.of (fun a b : Fin n =>
        (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R)) = 1 + strictOf R n x := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [hs x a a (lt_irrefl a)]
      · simp [hab, strictOf]
    rw [this]
    change above R n (u * (1 + strictOf R n x)) = _
    have h2 : u * (1 + strictOf R n x) = u + (strictOf R n x + (u - 1) * strictOf R n x) := by
      noncomm_ring
    rw [h2, map_add (f := _), map_add (f := _), has]
    rfl


open GlobalTheory.GaugeEx in
theorem map_unitri_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) (μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E)), μU.IsAddHaarMeasure → ∀ u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → μU.map (fun (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}) => (u * Matrix.of (fun a b : Fin (r + 1) => (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E))) p.1.1 p.1.2) = μU := by
  intro F E _ _ _ _ _ v r μ hμ u h1 h0
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨N, hN, hx⟩ := exists_nilpotent u h1 h0
  have hN' : IsNilpotent (N.restrictScalars (Fv F v) : Module.End (Fv F v) _) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun x => ?_⟩
    have := LinearMap.congr_fun hm x
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h2 := map_add_nilpotent μ _ hN'
  have hc : Continuous fun x => x + N.restrictScalars (Fv F v) x :=
    continuous_id.add (IsModuleTopology.continuous_of_linearMap _)
  rw [funext hx]
  refine Eq.trans ?_ (map_add_left_eq_self μ (above _ (r + 1) u))
  conv_rhs => rw [← h2]
  rw [Measure.map_map (measurable_const_add _) hc.measurable]
  rfl

end GlobalTheory.UnitriHaar
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem exists_equiv_ker_prod {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (ψ : M →ₗ[O] O) (hψ : Function.Surjective ψ) :
    ∃ E : M ≃ₗ[O] (LinearMap.ker ψ × O), ∀ x, (E x).2 = ψ x := by
  obtain ⟨x₀, hx₀⟩ := hψ 1
  let p : M →ₗ[O] LinearMap.ker ψ :=
    LinearMap.codRestrict _ (LinearMap.id - LinearMap.toSpanSingleton O M x₀ ∘ₗ ψ)
      (fun x => by simp [hx₀])
  refine ⟨LinearEquiv.ofLinearMap (p.prod ψ)
    ((LinearMap.ker ψ).subtype.coprod (LinearMap.toSpanSingleton O M x₀)) ?_ ?_, fun x => rfl⟩
  · apply LinearMap.prod_ext
    · ext y
      · simp [p]
      · simp
    · ext
      · simp [p, hx₀]
      · simp [hx₀]
  · ext x
    simp [p]

theorem exists_equiv_comp_eq_of_surjective {O M M' : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    [Module.Free O M] [Module.Finite O M] [Module.Free O M'] [Module.Finite O M']
    (h : Module.finrank O M = Module.finrank O M')
    (ψ : M →ₗ[O] O) (hψ : Function.Surjective ψ)
    (ψ' : M' →ₗ[O] O) (hψ' : Function.Surjective ψ') :
    ∃ e : M ≃ₗ[O] M', ∀ x, ψ' (e x) = ψ x := by
  obtain ⟨E, hE⟩ := exists_equiv_ker_prod ψ hψ
  obtain ⟨E', hE'⟩ := exists_equiv_ker_prod ψ' hψ'
  have hk : Module.finrank O (LinearMap.ker ψ) = Module.finrank O (LinearMap.ker ψ') := by
    have h₁ := E.finrank_eq
    have h₂ := E'.finrank_eq
    rw [Module.finrank_prod, Module.finrank_self] at h₁ h₂
    omega
  obtain ⟨k⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hk
  refine ⟨E.trans ((k.prodCongr (LinearEquiv.refl O O)).trans E'.symm), fun x => ?_⟩
  rw [← hE', ← hE]
  simp

theorem exists_form_of_covBy {O V : Type} [CommRing O] [IsLocalRing O] [AddCommGroup V]
    [Module O V] (A B : Submodule O V) [Module.Projective O B] (h : A ⋖ B) :
    ∃ ψ : B →ₗ[O] O, Function.Surjective ψ ∧
      ∀ x : B, (x : V) ∈ A ↔ ψ x ∈ IsLocalRing.maximalIdeal O := by
  have hs := (covBy_iff_quot_is_simple h.le).1 h
  obtain ⟨I, hI, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  set m := IsLocalRing.maximalIdeal O
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property m.mkQ
    (f.toLinearMap ∘ₗ (A.comap B.subtype).mkQ) m.mkQ_surjective
  have key : ∀ x, m.mkQ (ψ x) = f ((A.comap B.subtype).mkQ x) := fun x =>
    LinearMap.congr_fun hψ x
  have hmem : ∀ x : B, (x : V) ∈ A ↔ ψ x ∈ m := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero m, ← Submodule.mkQ_apply, key,
      LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply]
  refine ⟨ψ, ?_, hmem⟩
  obtain ⟨y, hy⟩ := f.surjective (m.mkQ 1)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  have hu : IsUnit (ψ x) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hx
    have h1 : m.mkQ 1 = 0 := by
      rw [← hy, ← key, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  intro r
  refine ⟨(r * hu.unit⁻¹.1) • x, ?_⟩
  rw [map_smul, smul_eq_mul, mul_assoc, hu.val_inv_mul, mul_one]

theorem exists_extend_latticeEquiv {O K V : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (B B' : Submodule O V) [B.IsFullLattice K] [B'.IsLattice K] (e : B ≃ₗ[O] B') :
    ∃ g : V ≃ₗ[K] V, ∀ x : B, g x = e x := by
  have := Submodule.IsLattice.finite K B
  have := Submodule.IsLattice.free K B
  have : B'.IsFullLattice K := Submodule.IsFullLattice.of_rank_le K B' (by
    rw [← Submodule.IsFullLattice.rank_eq K B, e.rank_eq])
  let b := Module.Free.chooseBasis O B
  let c := b.map e
  let g := (b.extendOfIsFullLattice K).equiv (c.extendOfIsFullLattice K) (Equiv.refl _)
  refine ⟨g, fun x => ?_⟩
  have key : (g.toLinearMap.restrictScalars O) ∘ₗ B.subtype = B'.subtype ∘ₗ e.toLinearMap := by
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, Submodule.coe_subtype, g, c]
    rw [← Module.Basis.extendOfIsFullLattice_apply K b i, Module.Basis.equiv_apply]
    simp
  exact LinearMap.congr_fun key x

theorem exists_conj_of_covBy : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ) (A B A' B' : Submodule O (Fin n → K)), B.FG → B'.FG → Submodule.span K (A : Set (Fin n → K)) = ⊤ → Submodule.span K (A' : Set (Fin n → K)) = ⊤ → A ⋖ B → A' ⋖ B' → ∃ g : GL (Fin n) K, (∀ x, x ∈ A ↔ g.1 *ᵥ x ∈ A') ∧ ∀ x, x ∈ B ↔ g.1 *ᵥ x ∈ B' := by
  intro O K _ _ _ _ _ _ n A B A' B' hB hB' hA hA' h h'
  have : B.IsLattice K := Submodule.IsLattice.of_fg K hB
  have : B'.IsLattice K := Submodule.IsLattice.of_fg K hB'
  have : B.IsFullLattice K :=
    ⟨eq_top_iff.2 (hA ▸ Submodule.span_mono (show (A : Set (Fin n → K)) ⊆ B from h.le))⟩
  have : B'.IsFullLattice K :=
    ⟨eq_top_iff.2 (hA' ▸ Submodule.span_mono (show (A' : Set (Fin n → K)) ⊆ B' from h'.le))⟩
  have : Module.Free O B := Submodule.IsLattice.free K B
  have : Module.Free O B' := Submodule.IsLattice.free K B'
  have : Module.Finite O B := Submodule.IsLattice.finite K B
  have : Module.Finite O B' := Submodule.IsLattice.finite K B'
  have hr : Module.finrank O B = Module.finrank O B' := by
    rw [((Submodule.IsFullLattice.finrank_eq K B).trans (Module.finrank_fintype_fun_eq_card K)), ((Submodule.IsFullLattice.finrank_eq K B').trans (Module.finrank_fintype_fun_eq_card K))]
  obtain ⟨ψ, hψs, hψ⟩ := exists_form_of_covBy A B h
  obtain ⟨ψ', hψs', hψ'⟩ := exists_form_of_covBy A' B' h'
  obtain ⟨e, he⟩ := exists_equiv_comp_eq_of_surjective hr ψ hψs ψ' hψs'
  obtain ⟨g, hg⟩ := exists_extend_latticeEquiv (K := K) B B' e
  have hBg : ∀ x, x ∈ B ↔ g x ∈ B' := by
    intro x
    constructor
    · intro hx
      rw [show g x = e ⟨x, hx⟩ from hg ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · intro hx
      have hy : ((e.symm ⟨g x, hx⟩ : B) : Fin n → K) = x :=
        g.injective (by rw [hg]; simp)
      rw [← hy]
      exact (e.symm _).2
  have hpt : ∀ x (hx : x ∈ B), (⟨g x, (hBg x).1 hx⟩ : B') = e ⟨x, hx⟩ := fun x hx =>
    Subtype.ext (hg ⟨x, hx⟩)
  let G : GL (Fin n) K :=
    ⟨LinearMap.toMatrix' g.toLinearMap, LinearMap.toMatrix' g.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hG : ∀ x, G.1 *ᵥ x = g x := fun x => LinearMap.toMatrix'_mulVec _ x
  refine ⟨G, fun x => ?_, fun x => ?_⟩
  · rw [hG]
    constructor
    · intro hx
      have hxB := h.le hx
      have hgB := (hBg x).1 hxB
      rw [hψ' ⟨g x, hgB⟩, hpt x hxB, he]
      exact (hψ ⟨x, hxB⟩).1 hx
    · intro hx
      have hgB := h'.le hx
      have hxB := (hBg x).2 hgB
      rw [hψ ⟨x, hxB⟩, ← he, ← hpt x hxB]
      exact (hψ' ⟨g x, hgB⟩).1 hx
  · rw [hG]
    exact hBg x

end GlobalTheory.St.G
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

noncomputable def conjLinearCombination {M : Type} [AddCommGroup M] [Module ℂ M] {I : Type}
    (b : I → M) : (I →₀ ℂ) →ₗ⋆[ℂ] M where
  toFun c := c.sum fun i x => star x • b i
  map_add' c d := by
    rw [Finsupp.sum_add_index']
    · intro i; simp
    · intro i x y; rw [star_add, add_smul]
  map_smul' r c := by
    rw [Finsupp.sum_smul_index' (by intro i; simp), Finsupp.smul_sum]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [smul_smul, smul_eq_mul, star_mul', starRingEnd_apply]

theorem conjLinearCombination_single {M : Type} [AddCommGroup M] [Module ℂ M] {I : Type}
    (b : I → M) (i : I) (x : ℂ) :
    conjLinearCombination b (Finsupp.single i x) = star x • b i := by
  change (Finsupp.single i x).sum (fun i x => star x • b i) = _
  rw [Finsupp.sum_single_index]; simp

theorem exists_conjLinear_of_gram_eq :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Type) [AddCommGroup M] [Module ℂ M] (N : M → M → ℂ) (I : Type) (a : I → W) (b : I → M), (∀ p p' q, N (p + p') q = N p q + N p' q) → (∀ (c : ℂ) p q, N (c • p) q = c * N p q) → (∀ p q, N q p = star (N p q)) → (∀ p, N p p = 0 → p = 0) → Submodule.span ℂ (Set.range a) = ⊤ → (∀ i j, N (b j) (b i) = ⟪a j, a i⟫_ℂ) → ∃ Jm : W →ₗ⋆[ℂ] M, (∀ i, Jm (a i) = b i) ∧ ∀ ξ η, N (Jm η) (Jm ξ) = ⟪η, ξ⟫_ℂ := by
  intro W _ _ M _ _ N I a b hadd hsmul hstar hdef hspan hgram
  have hadd2 : ∀ p q q', N p (q + q') = N p q + N p q' := by
    intro p q q'
    rw [hstar (q + q') p, hadd, star_add, ← hstar, ← hstar]
  have hsmul2 : ∀ (c : ℂ) p q, N p (c • q) = star c * N p q := by
    intro c p q
    rw [hstar (c • q) p, hsmul, star_mul', ← hstar]
  have hz1 : ∀ q, N 0 q = 0 := by
    intro q
    have := hsmul 0 0 q
    simpa using this
  have hz2 : ∀ p, N p 0 = 0 := by
    intro p
    rw [hstar 0 p, hz1, star_zero]
  set A := Finsupp.linearCombination ℂ a with hA
  set B := conjLinearCombination b with hB
  have key : ∀ c d, N (B c) (B d) = ⟪A c, A d⟫_ℂ := by
    intro c d
    induction c using Finsupp.induction_linear with
    | zero => simp [hz1]
    | add c c' h h' => rw [map_add (f := _), map_add (f := _), hadd, inner_add_left, h, h']
    | single i x =>
      induction d using Finsupp.induction_linear with
      | zero => simp [hz2]
      | add d d' h h' => rw [map_add (f := _), map_add (f := _), hadd2, inner_add_right, h, h']
      | single j y =>
        rw [hA, hB, conjLinearCombination_single, conjLinearCombination_single,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, hsmul, hsmul2,
          inner_smul_left, inner_smul_right, hgram, star_star, starRingEnd_apply]
  have hr : LinearMap.range A = ⊤ := by
    rw [hA, Finsupp.range_linearCombination, hspan]
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective A hr
  have hs' : ∀ w, A (s w) = w := fun w => LinearMap.congr_fun hs w
  refine ⟨B.comp s, fun i => ?_, fun ξ η => ?_⟩
  · have h0 : B (s (a i) - Finsupp.single i 1) = 0 := by
      apply hdef
      have : A (s (a i) - Finsupp.single i 1) = 0 := by
        rw [map_sub, hs', hA, Finsupp.linearCombination_single, one_smul, sub_self]
      rw [key, this, inner_zero_left]
    rw [map_sub, sub_eq_zero, hB, conjLinearCombination_single, star_one, one_smul] at h0
    exact h0
  · change N (B (s η)) (B (s ξ)) = _
    rw [key, hs', hs']

end GlobalTheory
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.exists_conjLinear_of_gram_eq' : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Type) [AddCommGroup M] [Module ℂ M] (N : M → M → ℂ) (I : Type) (a : I → W) (b : I → M), (∀ p p' q, N (p + p') q = N p q + N p' q) → (∀ (c : ℂ) p q, N (c • p) q = c * N p q) → (∀ p q, N q p = star (N p q)) → (∀ p, N p p = 0 → p = 0) → Submodule.span ℂ (Set.range a) = ⊤ → (∀ i j, N (b j) (b i) = ⟪a j, a i⟫_ℂ) → ∃ Jm : W →ₗ⋆[ℂ] M, (∀ i, Jm (a i) = b i) ∧ ∀ ξ η, N (Jm η) (Jm ξ) = ⟪η, ξ⟫_ℂ := by
  first | exact @GlobalTheory.exists_conjLinear_of_gram_eq | exact GlobalTheory.exists_conjLinear_of_gram_eq | (intros; apply GlobalTheory.exists_conjLinear_of_gram_eq <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_GL_conj_lattice_pairs_covBy_dvr : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ) (A B A' B' : Submodule O (Fin n → K)), B.FG → B'.FG → Submodule.span K (A : Set (Fin n → K)) = ⊤ → Submodule.span K (A' : Set (Fin n → K)) = ⊤ → A ⋖ B → A' ⋖ B' → ∃ g : GL (Fin n) K, (∀ x, x ∈ A ↔ g.1 *ᵥ x ∈ A') ∧ ∀ x, x ∈ B ↔ g.1 *ᵥ x ∈ B' := by
  first | exact @GlobalTheory.St.G.exists_conj_of_covBy | exact GlobalTheory.St.G.exists_conj_of_covBy | (intros; apply GlobalTheory.St.G.exists_conj_of_covBy <;> assumption)

end
end
