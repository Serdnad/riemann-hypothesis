module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle002
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularIndex.PairwiseDisjointCosets
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem emb_add (c c' : ι → B) : emb b (c + c') = emb b c + emb b c' := by
  apply coord_injective b; rw [map_add (f := _), coord_emb, coord_emb, coord_emb]

theorem emb_zero : emb b (0 : ι → B) = 0 := by
  apply coord_injective b; rw [map_zero, coord_emb]

theorem emb_neg (c : ι → B) : emb b (-c) = -emb b c := by
  apply coord_injective b; rw [map_neg, coord_emb, coord_emb]

theorem emb_sub (c c' : ι → B) : emb b (c - c') = emb b c - emb b c' := by
  apply coord_injective b; rw [map_sub, coord_emb, coord_emb, coord_emb]

theorem emb_nsmul (N : ℕ) (c : ι → B) : emb b (N • c) = N • emb b c := by
  apply coord_injective b; rw [map_nsmul, coord_emb, coord_emb]

theorem isClosed_eqA [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] {X : Type*} [TopologicalSpace X]
    {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = {p | coord b (f p) = coord b (g p)} := by
    ext p; exact (coord_injective b).eq_iff.symm
  rw [this]; exact isClosed_eq hf hg

end General

namespace Cpt

variable (I : AutInst)

abbrev ιb : Type := Fin (Module.finrank I.F I.E)

abbrev bs : Module.Basis (ιb I) I.F I.E := Module.finBasis I.F I.E

abbrev Co : Type := Fin I.n → Fin I.n → ιb I → Af I.F

def matOf (P : Co I) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun i j => emb (bs I) (P i j)

theorem mulVec_mem_Lf (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ l ∈ I.L, M *ᵥ inclV (F := I.F) l ∈ I.Lf) : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨l, hl⟩, rfl⟩ := hx; exact hM l hl
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hx

theorem isClosed_LfC (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F,
      (∀ j k, coord (bs I) (y j) k ∈ Ohat I.F) → d • y ∈ I.Lf) :
    IsClosed {w : Fin I.n → ιb I → Af I.F | (fun j => emb (bs I) (w j)) ∈ I.Lf} := by
  let S : AddSubgroup (Fin I.n → ιb I → Af I.F) :=
    { carrier := {w | (fun j => emb (bs I) (w j)) ∈ I.Lf}
      add_mem' := fun {w w'} hw hw' => by
        have : (fun j => emb (bs I) ((w + w') j)) = (fun j => emb (bs I) (w j)) + fun j => emb (bs I) (w' j) := by
          funext j; simp [emb_add]
        show (fun j => emb (bs I) ((w + w') j)) ∈ I.Lf
        rw [this]; exact I.Lf.add_mem hw hw'
      zero_mem' := by
        show (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) ∈ I.Lf
        have : (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) = 0 := by
          funext j; simp [emb_zero]
        rw [this]; exact I.Lf.zero_mem
      neg_mem' := fun {w} hw => by
        have : (fun j => emb (bs I) ((-w) j)) = -fun j => emb (bs I) (w j) := by
          funext j; simp [emb_neg]
        show (fun j => emb (bs I) ((-w) j)) ∈ I.Lf
        rw [this]; exact I.Lf.neg_mem hw }
  have hnhds : (S : Set (Fin I.n → ιb I → Af I.F)) ∈ 𝓝 0 := by
    let U := {w : Fin I.n → ιb I → Af I.F | ∀ j k, algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k ∈ Ohat I.F}
    have hU : IsOpen U := by
      have : U = ⋂ j, ⋂ k, (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) ⁻¹' Ohat I.F := by
        ext w; simp [U]
      rw [this]
      refine isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have hc : Continuous (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) :=
        continuous_const.mul ((continuous_apply k).comp (continuous_apply j))
      exact hc.isOpen_preimage _ isOpen_Ohat
    have h0 : (0 : Fin I.n → ιb I → Af I.F) ∈ U := fun j k => by simpa using ohat_zero
    refine Filter.mem_of_superset (hU.mem_nhds h0) fun w hw => ?_
    have hd0 : (d : I.F) ≠ 0 := by exact_mod_cast hd.ne'
    have := hlow (fun j => emb (bs I) (fun k => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k))
      (fun j k => by rw [coord_emb]; exact hw j k)
    show (fun j => emb (bs I) (w j)) ∈ I.Lf
    convert this using 1
    funext j
    rw [Pi.smul_apply, ← emb_nsmul]
    congr 1; funext k
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul,
      mul_inv_cancel₀ hd0, map_one, one_mul]
  exact AddSubgroup.isClosed_of_isOpen S (S.isOpen_of_mem_nhds hnhds)

end Cpt

end PI.WAU
end
end

section

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def ohatL (L : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → E ⊗[F] Af F) :=
  AddSubgroup.closure {y | ∃ c ∈ Ohat F, ∃ l ∈ L, y = ((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) (Af F) (l i)}

theorem smul_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {a : E ⊗[F] Af F} (ha : a ∈ IntAf F E) :
    ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L := by
  let T : Subring (E ⊗[F] Af F) :=
    { carrier := {a | ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L}
      mul_mem' := fun {a c} ha hc y hy => by rw [mul_smul]; exact ha _ (hc y hy)
      one_mem' := fun y hy => by rw [one_smul]; exact hy
      add_mem' := fun {a c} ha hc y hy => by rw [add_smul]; exact add_mem (ha y hy) (hc y hy)
      zero_mem' := fun y _ => by rw [zero_smul]; exact zero_mem _
      neg_mem' := fun {a} ha y hy => by rw [neg_smul]; exact neg_mem (ha y hy) }
  have hle : IntAf F E ≤ T := by
    apply Subring.closure_le.mpr
    rintro a (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c, hc, o • l, L.smul_mem o hl, ?_⟩
        funext i
        show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Af F)) * (((1 : E) ⊗ₜ[F] c) * ((l i) ⊗ₜ[F] (1 : Af F))) =
          ((1 : E) ⊗ₜ[F] c) * (((o • l) i) ⊗ₜ[F] (1 : Af F))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Pi.smul_apply, Algebra.smul_def]
        simp only [one_mul, mul_one]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
    · refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
  exact hle ha

theorem lamAf_le_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af F}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨1, ohat_one, (l : Fin n → E), l.2, ?_⟩
    rw [← Algebra.TensorProduct.one_def, one_smul]
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul a x _ hx => exact smul_ohatL L a.2 x hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem intC_zero {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af F) := by
  intro k
  simp only [map_zero, Pi.zero_apply]
  exact ohat_zero

theorem intC_neg {b : Module.Basis ι F E} {x : E ⊗[F] Af F} (hx : IntC b x) : IntC b (-x) := by
  intro k
  simp only [map_neg, Pi.neg_apply]
  exact ohat_neg (hx k)

theorem exists_upper (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by
  obtain ⟨T, hT⟩ := (hfg.restrictScalars (R := ℤ))
  obtain ⟨D, hD, hDint⟩ := exists_den_fin (fun x : T × Fin n × ι =>
    b.repr ((x.1 : Fin n → E) x.2.1) x.2.2)
  have hQ : ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
    intro l hl
    have hl' : l ∈ Submodule.span ℤ (T : Set (Fin n → E)) := by rw [hT]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem x hx => intro j k; exact hDint ⟨⟨x, hx⟩, j, k⟩
    | zero =>
      intro j k
      unfold IntF
      simp only [Pi.zero_apply, map_zero, Finsupp.coe_zero, mul_zero]
      exact ohat_zero
    | add x z _ _ hx hz =>
      intro j k
      have h1 := hx j k
      have h2 := hz j k
      unfold IntF at h1 h2 ⊢
      rw [Pi.add_apply, map_add (f := _), Finsupp.add_apply, mul_add, map_add (f := _)]
      exact ohat_add h1 h2
    | smul a x _ hx =>
      intro j k
      have h1 := hx j k
      unfold IntF at h1 ⊢
      rw [Pi.smul_apply, map_zsmul, Finsupp.smul_apply, mul_smul_comm, map_zsmul]
      exact ohat_zsmul h1 a
  refine ⟨D, hD, fun y hy j => ?_⟩
  have hy' := lamAf_le_ohatL L hy
  clear hy
  unfold ohatL at hy'
  induction hy' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    intro k
    rw [map_nsmul, Pi.smul_apply]
    have ew : ((((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) (Af F) (l i)) j) =
        (l j) ⊗ₜ[F] c := by
      simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    rw [ew]
    simp only [coord, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, Algebra.smul_def]
    exact ohat_mul (hQ l hl j k) hc
  | zero => rw [Pi.zero_apply, smul_zero]; exact intC_zero
  | add u w _ _ hu hw => rw [Pi.add_apply, smul_add]; exact intC_add hu hw
  | neg u _ hu => rw [Pi.neg_apply, smul_neg]; exact intC_neg hu

end PI.WAU
end
end

section

noncomputable section

namespace PI.WAU

open Formalism.MainNotions.S MeasureTheory Matrix Pointwise

theorem kg_one_eq (I : AutInst) : I.Kg 1 = I.Kset := by
  ext x
  refine ⟨fun h => h.1, fun h => ⟨h, fun y hy => ⟨(I.fmat x - 1) *ᵥ y, ?_, by simp⟩⟩⟩
  have h' : ∀ y, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf := h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem ((h' y).1 hy) hy

theorem kset_open (I : AutInst) : IsOpen I.Kset := by
  rw [← kg_one_eq]
  exact I.topf_open 1 le_rfl

theorem ksub_coe (I : AutInst) : ((Ksub I : Subgroup I.Gf) : Set I.Gf) = I.Kset := rfl

theorem sigmaFinite_of_K (I : AutInst) (μ : Measure I.Gf) (hμ : μ.IsHaarMeasure)
    (hKc : IsCompact I.Kset) (hQ : ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset) :
    SigmaFinite μ := by
  haveI := hμ
  obtain ⟨s, hs, hcov⟩ := hQ
  refine Measure.sigmaFinite_of_countable (S := (fun y => (fun x => y * x) '' I.Kset) '' s)
    (hs.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    show μ ((fun x => y * x) '' I.Kset) < ⊤
    rw [Set.image_mul_left, measure_preimage_mul]
    exact hKc.measure_lt_top
  · rw [Set.sUnion_image, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hy, hyx⟩ := hcov x
    exact Set.mem_biUnion hy ⟨y⁻¹ * x, hyx, mul_inv_cancel_left y x⟩

theorem adUnimod_of (hA : KgSubgroup) (hC : KCompact) (hQ : KCountable) (hI : IndexEq) :
    PI.AdUnimod := by
  intro I μ hμ
  haveI := sigmaFinite_of_K I μ hμ (hC I) (hQ I)
  choose U hU using fun n : ℕ => hA I (n + 1) (by omega)
  refine PI.UnimodIdxWork.unimodIdx_main I.Gf μ hμ U (fun n => ?_) (fun V hV => ?_) (Ksub I) ?_ ?_ (hI I)
  · rw [hU n]
    exact I.topf_open (n + 1) (by omega)
  · obtain ⟨g, hg1, hgV⟩ := I.topf_basis V hV
    refine ⟨g - 1, ?_⟩
    rw [hU (g - 1), show g - 1 + 1 = g by omega]
    exact hgV
  · rw [ksub_coe]
    exact kset_open I
  · rw [ksub_coe]
    exact hC I

end PI.WAU
end
end
