module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem fgHom_mem_of_closed {G : Type} [Group G] [TopologicalSpace G] {s : Set G}
    (hs : TopGen s) (E : Subgroup G) (hE : IsClosed (E : Set G)) (hsE : s ⊆ E) (g : G) : g ∈ E := by
  have h1 : (Subgroup.closure s : Set G) ⊆ E := (Subgroup.closure_le E).2 hsE
  have h2 : closure (Subgroup.closure s : Set G) ⊆ E := closure_minimal h1 hE
  exact h2 (hs g)

private theorem fgHom_part1 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (Z : Type) [Group Z] [Finite Z] :
    {f : G →* Z | IsOpen (f.ker : Set G)}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun f : G →* Z => fun x : s => f x) (Set.toFinite _) ?_
  intro f hf f' hf' h
  have hle : f.ker ⊓ f'.ker ≤ f.eqLocus f' := by
    intro x hx
    have h1 : f x = 1 := hx.1
    have h2 : f' x = 1 := hx.2
    show f x = f' x
    rw [h1, h2]
  have hop : IsOpen ((f.ker ⊓ f'.ker : Subgroup G) : Set G) := IsOpen.inter hf hf'
  have hcl : IsClosed (f.eqLocus f' : Set G) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono hle hop)
  ext g
  exact fgHom_mem_of_closed hs _ hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part2 {G : Type} [Group G] [TopologicalSpace G]
    (hG : TopFG G) (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M] :
    {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun c : G → M => fun x : s => c x) (Set.toFinite _) ?_
  intro c hc c' hc' h
  have one : ∀ d : G → M, (∀ g h, d (g * h) = d g + g • d h) → d 1 = 0 := by
    intro d hd
    have := hd 1 1
    rw [one_mul, one_smul] at this
    exact left_eq_add.1 this
  let E : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := by
        intro a b ha hb
        have ha' : c a = c' a := ha
        have hb' : c b = c' b := hb
        show c (a * b) = c' (a * b)
        rw [hc.2, hc'.2, ha', hb']
      one_mem' := by
        show c 1 = c' 1
        rw [one c hc.2, one c' hc'.2]
      inv_mem' := by
        intro a ha
        have ha' : c a = c' a := ha
        show c a⁻¹ = c' a⁻¹
        have h1 := hc.2 a a⁻¹
        have h2 := hc'.2 a a⁻¹
        rw [mul_inv_cancel, one c hc.2] at h1
        rw [mul_inv_cancel, one c' hc'.2, ← ha'] at h2
        exact MulAction.injective a (add_left_cancel (h1.symm.trans h2)) }
  have hcl : IsClosed (E : Set G) := by
    have := (hc.1.prodMk hc'.1) {p : M × M | p.1 ≠ p.2}
    rw [← isOpen_compl_iff]
    exact this
  funext g
  exact fgHom_mem_of_closed hs E hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (n : ℕ) (hn : n ≠ 0) :
    {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite := by
  have h1 := (fgHom_part1 hG (Equiv.Perm (Fin n))).prod (Set.finite_univ (α := Fin n))
  refine (h1.image fun p => (MulAction.stabilizer (Equiv.Perm (Fin n)) p.2).comap p.1).subset ?_
  rintro H ⟨hH, hi⟩
  haveI : H.FiniteIndex := ⟨hi ▸ hn⟩
  have e : (G ⧸ H) ≃ Fin n := Finite.equivFinOfCardEq hi
  refine ⟨(e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H)), e ((1 : G) : G ⧸ H)),
    ⟨?_, trivial⟩, ?_⟩
  · have hop : IsOpen (H.normalCore : Set G) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (Subgroup.normalCore_isClosed H (Subgroup.isClosed_of_isOpen H hH))
    refine Subgroup.isOpen_mono ?_ hop
    intro g hg
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]
  · ext g
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    have : (e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))) g • e ((1 : G) : G ⧸ H)
        = e ((g : G) : G ⧸ H) := by
      simp [Equiv.Perm.smul_def]
    rw [this, e.injective.eq_iff, eq_comm, QuotientGroup.eq, inv_one, one_mul]

theorem UpperTheory.V.AlgebraTools.finite_hom_of_topFG :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], TopFG G →
      (∀ (Z : Type) [Group Z] [Finite Z], {f : G →* Z | IsOpen (f.ker : Set G)}.Finite) ∧
      (∀ (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M], (∀ m : M, IsLocallyConstant fun g : G => g • m) →
        {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite) ∧
      (∀ n : ℕ, n ≠ 0 → {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite) := by
  intro G _ _ _ hG
  exact ⟨fun Z _ _ => fgHom_part1 hG Z, fun M _ _ _ _ => fgHom_part2 hG M,
    fun n hn => fgHom_part3 hG n hn⟩
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_exist :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {F : Type} [CommRing F] [Algebra B F] [HenselianRing B (RingHom.ker (algebraMap B F))] {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (r : E →ₐ[B] Matrix ι ι F) (ep : ι → E), IsUnit (2 : B) → (∀ i, o (o i) = o i) → (∀ x, r (T.st x) = (r x)ᵀ) → (∀ i, ∃ y, r y = single (o i) i 1) → CompleteOrthogonalIdempotents ep → (∀ i, T.st (ep i) = ep i) → (∀ i, r (ep i) = single i i 1) → (∀ i, T.tr (ep i) = 1) → (∀ i y, ∃ b : B, ep i * y * ep i = b • ep i) → ∃ U : T.Units ι o, U.ep = ep ∧ ∀ i, r (U.x i) = single (o i) i 1 := by
  intro B E _ _ _ T F _ _ _ ι _ _ o r ep h2 ho hr hy hco hst hre htr hrank
  have idem : ∀ i, ep i * ep i = ep i := fun i => (hco.idem i).eq
  have idem' : ∀ i x, ep i * (ep i * x) = ep i * x := fun i x => by rw [← mul_assoc, idem]
  choose y hy using hy
  obtain ⟨z, hz⟩ : ∃ z : ι → E, ∀ i, z i = ep (o i) * y i * ep i := ⟨_, fun i => rfl⟩
  have hz_mem : ∀ i, ep (o i) * z i * ep i = z i := by
    intro i
    rw [hz]
    simp only [mul_assoc, idem, idem']
  have hstz : ∀ i, T.st (z i) = ep i * (T.st (y i) * ep (o i)) := by
    intro i
    rw [hz, T.st_mul, T.st_mul, hst, hst]
  have hrz : ∀ i, r (z i) = single (o i) i 1 := by
    intro i
    rw [hz, map_mul, map_mul, hre, hre, hy]
    simp only [Matrix.single_mul_single_same, mul_one]
  choose b hb using fun i => hrank i (T.st (y i) * ep (o i) * y i)
  choose b' hb2 using fun i => hrank (o i) (y i * ep i * T.st (y i))
  have hb' : ∀ i, T.st (z i) * z i = b i • ep i := by
    intro i
    rw [hstz, hz, ← hb i]
    simp only [mul_assoc, idem, idem']
  have hzst : ∀ i, z i * T.st (z i) = b' i • ep (o i) := by
    intro i
    rw [hstz, hz, ← hb2 i]
    simp only [mul_assoc, idem, idem']
  have hbb : ∀ i, b' i = b i := by
    intro i
    have h := congrArg T.tr (hzst i)
    rw [T.tr_comm, hb', map_smul, map_smul, htr, htr, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h
    exact h.symm
  have hbF : ∀ i, algebraMap B F (b i) = 1 := by
    intro i
    have h := congrArg r (hb' i)
    rw [map_mul, hr, hrz, map_smul, hre, Matrix.transpose_single, Matrix.single_mul_single_same,
      mul_one] at h
    have h' := congrArg (fun M : Matrix ι ι F => M i i) h
    simp only [Matrix.smul_apply, Matrix.single_apply_same, Algebra.smul_def, mul_one] at h'
    exact h'.symm
  have hb1 : ∀ i, b i - 1 ∈ RingHom.ker (algebraMap B F) := by
    intro i
    rw [RingHom.mem_ker, map_sub, hbF, map_one, sub_self]
  choose α hα hα1 using fun i => UpperTheory.V.AlgebraTools.sqrt_one_add (RingHom.ker (algebraMap B F)) (b i) h2 (hb1 i)
  have hαinvF : ∀ i, algebraMap B F (↑(α i)⁻¹ : B) = 1 := by
    intro i
    have h1 := hα1 i
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
    have h := congrArg (algebraMap B F) (Units.inv_mul (α i))
    rw [map_mul, map_one, h1, mul_one] at h
    exact h
  have hinv : ∀ i, (↑(α i)⁻¹ : B) * ↑(α i)⁻¹ * b i = 1 := by
    intro i
    rw [← hα, sq, mul_assoc, ← mul_assoc (↑(α i)⁻¹ : B) (↑(α i)) (↑(α i)), Units.inv_mul, one_mul,
      Units.inv_mul]
  refine ⟨⟨ep, fun i => if o i = i then ep i else (↑(α i)⁻¹ : B) • z i, ho, hco, hst, htr, hrank,
    ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, h, idem, idem]
    · rw [if_neg h, mul_smul_comm, smul_mul_assoc, hz_mem]
  · intro i
    rw [if_pos (ho i)]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem, h]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hzst, hbb, smul_smul, hinv,
        one_smul]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hb', smul_smul, hinv, one_smul]
  · intro i
    dsimp only
    by_cases h : o i = i
    · rw [if_pos h, hre, h]
    · rw [if_neg h, map_smul, hrz, ← algebraMap_smul (A := F), hαinvF, one_smul]
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.trinv_baseChange :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) (B' : Type) [CommRing B'] [Algebra B B'], ∃ T' : TrInv B' (B' ⊗[B] E), (∀ y, T'.st (1 ⊗ₜ y) = 1 ⊗ₜ T.st y) ∧ ∀ y, T'.tr (1 ⊗ₜ y) = algebraMap B B' (T.tr y) := by
  intro B E _ _ _ T B' _ _
  let s : B' ⊗[B] E →ₗ[B'] B' ⊗[B] E := T.st.baseChange B'
  let t : B' ⊗[B] E →ₗ[B'] B' :=
    (AlgebraTensorModule.rid B B' B').toLinearMap ∘ₗ T.tr.baseChange B'
  have hs : ∀ (a : B') (y : E), s (a ⊗ₜ y) = a ⊗ₜ T.st y := fun a y => by simp [s]
  have ht : ∀ (a : B') (y : E), t (a ⊗ₜ y) = T.tr y • a := fun a y => by simp [t]
  refine ⟨⟨s, ?_, ?_, t, ?_, ?_⟩, fun y => hs 1 y, fun y => ?_⟩
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, hs, T.st_mul, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, T.st_st]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, ht, T.tr_comm u v, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, ht, T.tr_st]
  · show t (1 ⊗ₜ y) = _
    rw [ht, Algebra.algebraMap_eq_smul_one]
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.chartGen_cotInd :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι B) (m l : ι → B) (c : ι),
      CotInd B (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → l c = 1 →
      CotInd B (Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c)) := by
  intro B _ _ ι _ _ z m l c hx hl
  have hmem := hx.mem
  refine ⟨?_, ?_⟩
  · intro k
    rcases k with i | j
    · simp only [Sum.elim_inl, Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hmem (Sum.inl (i, j)))
    · simp only [Sum.elim_inr]
      exact Ideal.sub_mem _ (hmem (Sum.inr j.1)) (Ideal.mul_mem_left _ _ (hmem (Sum.inr c)))
  · intro a ha
    let b : ι × ι ⊕ ι → B := Sum.elim (fun ij => a (Sum.inl ij.1) * l ij.2)
      (fun j => if h : j = c then -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1)
        else a (Sum.inr ⟨j, h⟩))
    have key : ∑ k, b k * Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m k
        = ∑ k, a k * Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c) k := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => b (Sum.inr j) * m j) c]
      simp only [b, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, dite_true]
      have e : ∀ j : {j // j ≠ c}, (if h : (j : ι) = c then
          -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1) else a (Sum.inr ⟨j, h⟩)) * m j
          = a (Sum.inr j) * m j := fun j => by rw [dite_eq_right j.2]
      rw [Finset.sum_congr rfl (fun j _ => e j)]
      have e2 : ∀ i, ∑ j, a (Sum.inl i) * l j * z i j = a (Sum.inl i) * ∑ j, z i j * l j := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [Finset.sum_congr rfl (fun i _ => e2 i)]
      have e3 : ∑ j : {j // j ≠ c}, a (Sum.inr j) * (m j - l j * m c)
          = ∑ j : {j // j ≠ c}, a (Sum.inr j) * m j - (∑ k : {k // k ≠ c}, a (Sum.inr k) * l k) * m c := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e3]
      ring
    have hb : ∀ k, b k ∈ maximalIdeal B := hx.indep b (by rw [key]; exact ha)
    intro k
    rcases k with i | j
    · have := hb (Sum.inl (i, c))
      simpa [b, hl] using this
    · have := hb (Sum.inr j.1)
      simpa [b, j.2] using this
end

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.dual_lattice_denom {A : Type} [CommRing A] [IsDomain A]
    {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V]
    [Module A V] [IsScalarTower A F V] (Y : Submodule A V) (hY : Submodule.IsFullLattice F Y)
    (z : V) : ∃ a : A, a ≠ 0 ∧ a • z ∈ Y :=
  _root_.UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom Y hY z

private theorem UpperTheory.V.AlgebraTools.dual_lattice_pow {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (a : A) (ha : a ≠ 0) :
    ∃ s : ℕ, maximalIdeal A ^ s ≤ Ideal.span {a} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact (Units.isUnit u).mul_left_dvd.mpr dvd_rfl

theorem UpperTheory.V.AlgebraTools.dual_lattice :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] (Bf : LinearMap.BilinForm F V), Bf.IsSymm → Bf.Nondegenerate → ∀ Y : Submodule A V, Submodule.IsFullLattice F Y → Submodule.IsFullLattice F (Bf.dualSubmodule Y) ∧ Bf.dualSubmodule (Bf.dualSubmodule Y) = Y ∧ ∀ Z : Submodule A V, Submodule.IsLattice F Z → ∃ s : ℕ, maximalIdeal A ^ s • Z ≤ Y := by
  intro A _ _ _ F V _ _ _ _ _ _ _ _ Bf hs hn Y hY
  classical
  haveI : Module.Free A Y := Submodule.IsLattice.free F Y
  haveI : Module.Finite A Y := Submodule.IsLattice.finite F Y
  let b0 := Module.Free.chooseBasis A Y
  let b := b0.extendOfIsFullLattice F
  have hb : Submodule.span A (Set.range b) = Y := by
    have : (b : _ → V) = Y.subtype ∘ b0 := by
      funext i; simp [b]
    rw [this, Set.range_comp, ← Submodule.map_span, b0.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis Bf hn b]
    exact { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _))
            span_eq_top := by rw [Submodule.span_span_of_tower, Module.Basis.span_eq] }
  · rw [← hb]
    exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis Bf hn hs b
  · intro Z hZ
    have hfg := hZ.fg
    clear hZ
    induction Z, hfg using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨a, ha, hax⟩ := UpperTheory.V.AlgebraTools.dual_lattice_denom Y hY x
      obtain ⟨s, hs⟩ := UpperTheory.V.AlgebraTools.dual_lattice_pow a ha
      refine ⟨s, (Submodule.smul_mono_left hs).trans ?_⟩
      refine Submodule.smul_le.mpr fun r hr y hy => ?_
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [mul_smul, smul_comm a c]
      exact Y.smul_mem _ (Y.smul_mem _ hax)
    | sup M N _ _ hM hN =>
      obtain ⟨s, hs⟩ := hM
      obtain ⟨t, ht⟩ := hN
      refine ⟨s + t, ?_⟩
      rw [Submodule.smul_sup]
      refine sup_le ?_ ?_
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right s t))).trans hs
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left t s))).trans ht
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkDedekind :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (K : Type) [Field K] [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (f : Perm (Fin n) → K),
      (∀ x : MvPolynomial (Fin n) R, ∑ u, f u * algebraMap _ K (rename u x) = 0) → f = 0 := by
  intro R _ _ n K _ _ _ f hf
  classical
  let φ : Perm (Fin n) → (MvPolynomial (Fin n) R →* K) := fun u =>
    (algebraMap (MvPolynomial (Fin n) R) K).toMonoidHom.comp (rename u : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).toRingHom.toMonoidHom
  have hinj : Function.Injective φ := by
    intro u v huv
    ext i
    have h := DFunLike.congr_fun huv (X i)
    simp only [φ, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_toRingHom, rename_X] at h
    have h2 := IsFractionRing.injective (MvPolynomial (Fin n) R) K h
    exact congrArg Fin.val (X_injective h2)
  have hli := (linearIndependent_monoidHom (MvPolynomial (Fin n) R) K).comp φ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext u
  apply hli f
  funext x
  simpa [φ, Finset.sum_apply] using hf x
end
