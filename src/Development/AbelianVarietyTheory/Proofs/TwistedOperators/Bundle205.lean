module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle198
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree.AdelCls

open GlobalTheory.Mass

theorem dc_iff {G H : Type} [Group G] [Group H] (f : G →* H) (Γ A L N : Subgroup G) (Q K : Subgroup H)
    (hQ : Γ.map f = Q) (hA : ∀ x, ∃ h ∈ A, f h = x) (hL : ∀ κ, κ ∈ L ↔ κ ∈ A ∧ f κ ∈ K)
    (hN : ∀ h, f h = 1 ↔ h ∈ N) (h h' : G) :
    (∃ x ∈ Q, ∃ k ∈ K, f h' = x * f h * k) ↔ ∃ γ ∈ Γ, ∃ κ ∈ L, ∃ k ∈ N, h' = γ * h * κ * k := by
  constructor
  · rintro ⟨x, hx, k, hk, e⟩
    rw [← hQ] at hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨κ, hκA, rfl⟩ := hA k
    refine ⟨γ, hγ, κ, (hL κ).2 ⟨hκA, hk⟩, (γ * h * κ)⁻¹ * h', (hN _).1 ?_,
      (mul_inv_cancel_left (γ * h * κ) h').symm⟩
    simp only [map_mul, map_inv, e, inv_mul_cancel]
  · rintro ⟨γ, hγ, κ, hκ, k, hk, rfl⟩
    refine ⟨f γ, ?_, f κ, ((hL κ).1 hκ).2, ?_⟩
    · rw [← hQ]
      exact Subgroup.mem_map_of_mem f hγ
    · rw [map_mul, map_mul, map_mul, (hN k).2 hk, mul_one]

variable {D : D7}

theorem finU_eq (V : HSp D) {π : GA D V →* HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram}
    (hπ : IsFinProj D.sp.cm.sig V.gram π) (h : GA D V) :
    finU V h = swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) := by
  apply Subtype.ext
  rw [coe_finU, coe_swapPts, hπ h]
  rfl

theorem finU_eq_one_iff (V : HSp D) (h : GA D V) : finU V h = 1 ↔ h ∈ GinfC V := by
  have hs : Function.Injective (swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective
  have hb : Function.Injective
      (Formalism.UG.bc (swapAE D) : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →* GL (Fin V.rank) (EAf D)) :=
    Units.map_injective (Matrix.map_injective hs)
  rw [← OneMemClass.coe_eq_one, coe_finU, GinfC, MonoidHom.mem_ker]
  change Formalism.UG.bc (swapAE D) (finHom V h) = 1 ↔ finHom V h = 1
  exact map_eq_one_iff _ hb

theorem exists_fin (V : HSp D) (x : UA D.sp.cm V.gram) : ∃ h ∈ GfC V, finU V h = x := by
  obtain ⟨hsp, hex⟩ := parts_spec (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram
  obtain ⟨y, rfl⟩ := (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective x
  obtain ⟨g, g1, g2⟩ := hex 1 (HA.mat _ _ _ y)
  have hg : g ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := by
    refine (hsp g).2 ⟨?_, ?_⟩
    · rw [g1]
      exact one_mem _
    · rw [g2]
      exact (y : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).2
  refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 g1, ?_⟩
  apply Subtype.ext
  rw [coe_swapPts, ← g2]
  rfl

theorem mem_levA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (κ : GA D V) :
    κ ∈ levA V K ↔ κ ∈ GfC V ∧ finU V κ ∈ K.subgroupOf (UA D.sp.cm V.gram) := by
  simp only [levA, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_finU]

theorem map_rat (V : HSp D) : (GQ V).map (finU V) = UQ D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  have e : finU V = (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram).comp π :=
    MonoidHom.ext fun h => finU_eq V hπ h
  have h1 : (GQ V).map π = ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram := hπ.map_ratIn
  rw [e, ← Subgroup.map_map, h1]
  exact map_swapPts_rat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram

theorem rat_mem (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) : finU V γ ∈ UQ D.sp.cm V.gram := by
  rw [← map_rat V]
  exact Subgroup.mem_map_of_mem _ hγ

theorem rat_inj (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (e : finU V γ = 1) : γ = 1 := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  rw [finU_eq V hπ, MulEquiv.map_eq_one_iff] at e
  exact hπ.injOn (SetLike.mem_coe.2 hγ) (SetLike.mem_coe.2 (Subgroup.one_mem _)) (by rw [e, map_one])

theorem adelic_classes : ∀ (D : D7) (V : HSp D), (∀ x : UA D.sp.cm V.gram, ∃ h ∈ GfC V, finU V h = x) ∧ (∀ γ ∈ GQ V, finU V γ ∈ UQ D.sp.cm V.gram) ∧ (∀ x ∈ UQ D.sp.cm V.gram, ∃ γ ∈ GQ V, finU V γ = x) ∧ (∀ γ ∈ GQ V, finU V γ = 1 → γ = 1) ∧ ∀ (K : Subgroup (GL (Fin V.rank) (EAf D))) (h h' : GA D V), clsA V K h = clsA V K h' ↔ ∃ γ ∈ GQ V, ∃ κ ∈ levA V K, ∃ k ∈ GinfC V, h' = γ * h * κ * k := by
  intro D V
  refine ⟨exists_fin V, rat_mem V, fun x hx => ?_, rat_inj V, fun K h h' => ?_⟩
  · rw [← map_rat V] at hx
    obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.1 hx
    exact ⟨γ, hγ, e⟩
  · first
      | rw [clsA, clsA, Quotient.eq'', DoubleCoset.rel_iff]
      | (show DoubleCoset.mk _ _ (finU V h) = DoubleCoset.mk _ _ (finU V h') ↔ _
         rw [DoubleCoset.eq])
    exact dc_iff (finU V) (GQ V) (GfC V) (levA V K) (GinfC V) (UQ D.sp.cm V.gram)
      (K.subgroupOf (UA D.sp.cm V.gram)) (map_rat V) (exists_fin V) (mem_levA V K) (finU_eq_one_iff V) h h'

end GlobalTheory.DefFree.AdelCls
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabDense

section Generic

theorem units_tendsto {M ι : Type} [Monoid M] [TopologicalSpace M] {l : Filter ι} {f : ι → Mˣ} {u : Mˣ}
    (h1 : Filter.Tendsto (fun i => (f i : M)) l (nhds (u : M)))
    (h2 : Filter.Tendsto (fun i => (((f i)⁻¹ : Mˣ) : M)) l (nhds ((u⁻¹ : Mˣ) : M))) :
    Filter.Tendsto f l (nhds u) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact h1.prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp h2)

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_mul {a b : A} (hab : a * b = 0) (m : Matrix n n A) :
    (a + b) • m + (1 - (a + b)) • (1 : Matrix n n A) =
      (a • m + (1 - a) • (1 : Matrix n n A)) * (b • m + (1 - b) • (1 : Matrix n n A)) := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  linear_combination (norm := module) hab • (2 • m - m * m - 1)

omit [Fintype n] in
theorem cut_entry (a : A) (m : Matrix n n A) (i j : n) :
    (a • m + (1 - a) • (1 : Matrix n n A)) i j = a * (m - 1) i j + (1 : Matrix n n A) i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

omit [Fintype n] in
theorem cut_supp {a : A} (ha : a * a = a) (m : Matrix n n A) (i j : n) :
    a * (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j = (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j := by
  rw [Matrix.sub_apply, cut_entry, add_sub_cancel_right, ← mul_assoc, ha]

theorem sum_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i, p i * p i = p i)
    (h0 : ∀ i j, i ≠ j → p i * p j = 0) : (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => h0 i j (Ne.symm hji)) (fun hi' => absurd hi hi'), h i]

end Generic

variable {D : D7}

theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε := by
  classical
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1), singleV D.host.F v 1, rfl, ?_, fun w hw => ?_⟩
  · exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1
  · exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hw

theorem placeIdem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, hα0⟩ := h
  obtain ⟨α', rfl, -, hα0'⟩ := h'
  have hz : α * α' = 0 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α' w = 0
    by_cases hw : w = v
    · have hw' : α' w = 0 := hα0' w (by rw [hw]; exact hv)
      rw [hw', mul_zero]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', zero_mul]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α' = pairA D.host.F (0 * 0) (α * α') from rfl, hz, mul_zero]
  rfl

theorem placeIdem_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε * ε = ε := by
  obtain ⟨α, rfl, hα1, hα0⟩ := h
  have hz : α * α = α := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α w = α w
    by_cases hw : w = v
    · have hw' : α w = 1 := by rw [hw]; exact hα1
      rw [hw', mul_one]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', mul_zero]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α = pairA D.host.F (0 * 0) (α * α) from rfl, hz, mul_zero]

theorem mt_inj (V : HSp D) {g h : GA D V} (e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) : g = h := by
  apply Subtype.ext
  apply Units.ext
  exact e

theorem tendsto_of_mt {ι : Type} {l : Filter ι} (V : HSp D) {f : ι → GA D V} {g : GA D V}
    (h1 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)) l (nhds (Formalism.L2.Theta.mt V g)))
    (h2 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)⁻¹) l (nhds (Formalism.L2.Theta.mt V g⁻¹))) :
    Filter.Tendsto f l (nhds g) := by
  have hind : Topology.IsInducing
      (Subtype.val : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram) → GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    Topology.IsInducing.subtypeVal
  exact hind.tendsto_nhds_iff.2 (units_tendsto h1 h2)

theorem infPart_entry (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  have h1 : infHom V g = 1 := (MonoidHom.mem_ker).1 hg
  have h2 := congrArg (fun x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) h1
  simp only [infHom, MonoidHom.comp_apply, Formalism.UG.bc] at h2
  have e1 : infPart D (Formalism.L2.Theta.mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := h2
  have e2 : infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.sub_apply, map_sub, e1, e2, sub_self]

theorem exists_trunc (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v))
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ κ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V → GA D V,
      (∀ g, κ ∅ g = 1) ∧
      (∀ v s (hv : v ∉ s) g, κ (Finset.cons v s hv) g = κ {v} g * κ s g) ∧
      (∀ v g, Stab V β g → Stab V β (κ {v} g) ∧ SuppPl (ε v) V (κ {v} g)) ∧
      ∀ g, Stab V β g → Filter.Tendsto (fun s => κ s g) Filter.atTop (nhds g) := by
  have hid : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)), (∑ v ∈ s, ε v) * (∑ v ∈ s, ε v) = ∑ v ∈ s, ε v :=
    fun s => sum_idem ε s (fun v => placeIdem_idem (hε v)) (fun v w hvw => placeIdem_mul (hε v) (hε w) hvw)
  choose K hK using fun s => GlobalTheory.T.idempotent_twisted_group_endomorphism D V β (∑ v ∈ s, ε v) (hid s)
  have hKm : ∀ s x, Formalism.L2.Theta.mt V (K s x) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) • Formalism.L2.Theta.mt V x +
      (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    fun s x => (hK s x).1
  refine ⟨fun s g => K s g, fun g => ?_, fun v s hv g => ?_, fun v g hg => ⟨(hK {v} g).2 hg, fun i j => ?_⟩, fun g hg => ?_⟩
  · apply mt_inj V
    rw [hKm, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add, GlobalTheory.AdelicLatMove.mt_one]
  · apply mt_inj V
    show Formalism.L2.Theta.mt V (K _ g) = Formalism.L2.Theta.mt V (K {v} g * K s g)
    rw [hKm, GlobalTheory.AdelicLatMove.mt_mul, hKm, hKm, Finset.sum_cons, Finset.sum_singleton, map_add (f := _)]
    apply cut_mul
    rw [← map_mul, Finset.mul_sum, Finset.sum_eq_zero (fun w hw => placeIdem_mul (hε v) (hε w) (fun hvw => hv (by rw [hvw]; exact hw))), map_zero]
  · show algebraMap (AF D.host.F) (AE D) (ε v) * (Formalism.L2.Theta.mt V (K {v} g) - 1) i j = (Formalism.L2.Theta.mt V (K {v} g) - 1) i j
    rw [hKm, Finset.sum_singleton]
    exact cut_supp (by rw [← map_mul, placeIdem_idem (hε v)]) _ i j
  · have key : ∀ x : GA D V, x ∈ GfC V →
        Filter.Tendsto (fun s => Formalism.L2.Theta.mt V (K s x)) Filter.atTop (nhds (Formalism.L2.Theta.mt V x)) := by
      intro x hx
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      simp only [hKm, cut_entry]
      have hlim := (GlobalTheory.T.tendsto_finitePlaceTruncation_adeleE D ε hε ((Formalism.L2.Theta.mt V x - 1) i j) (infPart_entry V hx i j)).add_const
        ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      have e : (Formalism.L2.Theta.mt V x - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j = Formalism.L2.Theta.mt V x i j := by
        rw [Matrix.sub_apply, sub_add_cancel]
      rw [e] at hlim
      exact hlim
    refine tendsto_of_mt V (key g hg.1) ?_
    simpa only [map_inv] using key g⁻¹ (inv_mem hg.1)

theorem mem_of_local (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (H : Subgroup (GA D S × GA D T)) (hH : IsClosed (H : Set (GA D S × GA D T)))
    (hloc : ∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H)
    (g : GA D S) (h : GA D T) (hg : Stab S βS g) (hh : Stab T βT h) : (g, h) ∈ H := by
  choose ε hε using fun v => exists_placeIdem (D := D) v
  obtain ⟨κS, hS0, hSc, hS1, hSt⟩ := exists_trunc ε hε S βS
  obtain ⟨κT, hT0, hTc, hT1, hTt⟩ := exists_trunc ε hε T βT
  have hmem : ∀ s, (κS s g, κT s h) ∈ H := by
    intro s
    induction s using Finset.cons_induction with
    | empty => rw [hS0, hT0]; exact H.one_mem
    | cons v s hv ih =>
      rw [hSc v s hv, hTc v s hv]
      exact H.mul_mem (hloc v (ε v) (hε v) _ _ (hS1 v g hg).1 (hT1 v h hh).1 (hS1 v g hg).2 (hT1 v h hh).2) ih
  exact hH.mem_of_tendsto ((hSt g hg).prodMk_nhds (hTt h hh)) (Filter.Eventually.of_forall hmem)

end GlobalTheory.StabDense

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_fockPolynomialIso_unitaryPair : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ := by
  first | exact @GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | exact GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | (intros; apply GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → Nontrivial R₂.HK.V → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → IsCoverIt R₁ R₂ B → ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  first | exact @GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | exact GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | (intros; apply GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt.GlueProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {a b : ℕ}


open Classical in
def rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ)

def ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : LPol b a →ₗ[ℂ] PolF D b a :=
  LinearMap.mulRight ℂ (rest τ P) ∘ₗ (MvPolynomial.rename (fun s => (τ, s))).toLinearMap

theorem ins_apply (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    ins τ P p = MvPolynomial.rename (fun s => (τ, s)) p * rest τ P := rfl

open Classical in
theorem glue_update (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    glue (Function.update P τ p) = ins τ P p := by
  rw [ins_apply, glue, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), rest]
  congr 1
  · rw [Function.update_self]
  · refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]

theorem glue_eq (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : glue P = ins τ P (P τ) := by
  classical
  rw [← glue_update, Function.update_eq_self]

theorem pderiv_other {τ ρ : D.what₂.Tau} (h : ρ ≠ τ) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (MvPolynomial.rename (fun s => (ρ, s)) p : PolF D b a) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p t hp =>
    rw [map_mul, Derivation.leibniz, hp, MvPolynomial.rename_X, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e
      exact h (congrArg Prod.fst e)

theorem pderiv_rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) :
    MvPolynomial.pderiv (τ, s) (rest τ P) = 0 := by
  classical
  unfold rest
  refine Finset.prod_induction _ (fun q : PolF D b a => MvPolynomial.pderiv (τ, s) q = 0) ?_ ?_ ?_
  · intro x y hx hy
    rw [Derivation.leibniz, hx, hy]; simp
  · simp
  · intro ρ hρ
    exact pderiv_other (Finset.ne_of_mem_erase hρ) s _

theorem pderiv_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (ins τ P p) = ins τ P (MvPolynomial.pderiv s p) := by
  classical
  have hinj : Function.Injective (fun s : Fin b × Fin a => (τ, s)) := fun x y e => congrArg Prod.snd e
  have := MvPolynomial.pderiv_rename hinj s p
  rw [ins_apply, ins_apply, Derivation.leibniz, pderiv_rest, ← this]
  simp [mul_comm]

theorem mul_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.X (τ, s) * ins τ P p = ins τ P (MvPolynomial.X s * p) := by
  rw [ins_apply, ins_apply, map_mul, MvPolynomial.rename_X, mul_assoc]

theorem rai_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : raiO τ ε ε' i j (ins τ P p) = ins τ P (rai ε ε' i j p) := by
  unfold raiO rai
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.neg_apply, map_smul, map_neg, Derivation.coeFn_coe]
    rw [← pderiv_ins]

theorem low_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : lowO τ ε ε' i j (ins τ P p) = ins τ P (low ε ε' i j p) := by
  unfold lowO low
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe]
    rw [← pderiv_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]

theorem fockS_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (X : Matrix (Fin a) (Fin a) ℂ) (p : LPol b a) :
    fockS τ ε ε' X (ins τ P p) = ins τ P (locS ε ε' X p) := by
  unfold fockS locS

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add (f := _),
  Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem fockT_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin b) (Fin b) ℂ) (p : LPol b a) :
    fockT τ ε ε' Y (ins τ P p) = ins τ P (locT ε ε' Y p) := by
  unfold fockT locT

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add (f := _),
  Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem glue_span :
    Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | (apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue ..)

theorem glueLaw : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  intro D a b
  refine ⟨glue_span, fun τ ε ε' P => ⟨fun X => ?_, fun Y => ?_⟩⟩
  · rw [glue_update, glue_eq τ P, fockS_ins]
  · rw [glue_update, glue_eq τ P, fockT_ins]

end GlobalTheory.Chain.RealIt.GlueProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_contraction_isometric_discreteSeries_fock : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  first | exact @GlobalTheory.Chain.CoverContr.exists_isCoverIt | exact GlobalTheory.Chain.CoverContr.exists_isCoverIt | (intros; apply GlobalTheory.Chain.CoverContr.exists_isCoverIt <;> assumption)
end
