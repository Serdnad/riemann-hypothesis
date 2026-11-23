module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle324
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.FrameCongOpen

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def congInt (N : ℕ) : Subgroup (GL (Fin n) (Formalism.L2.Herm.intAf F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n)
    (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)}))).ker

theorem mem_congInt_span {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, z.1 a b - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b ∈
      Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)} := by
  rw [congInt, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [← Ideal.Quotient.eq]
  change Ideal.Quotient.mk _ (z.1 a b) = (1 : Matrix (Fin n) (Fin n) _) a b ↔ _
  simp only [Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem mem_congInt {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  have hone : ∀ a b, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b : Formalism.L2.Herm.intAf F E) :
      E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  rw [mem_congInt_span]
  refine forall₂_congr fun a b => ?_
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    rw [← hone, ← AddSubgroupClass.coe_sub, ← hc, Subring.coe_mul, Subring.coe_natCast, mul_comm]
  · rintro ⟨w, hw, e⟩
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, hone, e, mul_comm]

theorem mem_cong (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ)
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (N : E ⊗[F] Formalism.L2.Herm.Af F) * z) :
    x ∈ (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  exact ⟨y, (mem_congInt y).2 fun i j => h3 i j, hy⟩

theorem eventually_cong_mat (β : GL (Fin n) (E ⊗[F] Af F)) (N : ℕ) (hN : 0 < N) {X : Type} [TopologicalSpace X]
    {x₀ : X} {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈
      (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j,
      algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_cong β _ N ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro i j
    refine ⟨_, h3 i j, ?_⟩
    have hN' : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (N : ℕ) * (algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN', map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

def congFr (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  (congInt (F := F) (E := E) (n := n) N).map (frGL β)

theorem mem_congFr {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : ℕ} (hx : x ∈ congFr β N) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf F E), frGL β z = x ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 hx
  exact ⟨z, e, (mem_congInt z).1 hz⟩

end General

theorem exists_open_cong : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ κ ∈ U, ∃ z : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.frGL β z = Lev.finE V κ ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w := by
  intro D V β N hN
  refine ⟨(congFr β N).comap (Formalism.IndefR.Lev.finE V),
    ?_, fun κ hκ => ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hf : Continuous (finHom V) :=
      (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    exact eventually_cong_mat β N hN hf (map_one _)
  · exact mem_congFr (Subgroup.mem_comap.1 hκ)

end GlobalTheory.FrameCongOpen

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
open GlobalTheory.Doubling GlobalTheory.AdelicU

namespace GlobalTheory.Twist.OrthSum

variable {D : D7}

theorem pair_hsum (V W : HSp D) (x y : Fin (hsum V W).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (hsum V W).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * V.gram i j * y (finSumFinEquiv (Sum.inl j))) +
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * W.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hsum]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Doubling.blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

theorem selfDual_hsum {V W : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') :
    IsSelfDualC (hsum V W) (sumLat finSumFinEquiv L L') := by
  have hsumLat : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L') := by
    let φ : ((Fin V.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (V.rank + W.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L' =
        (L.prod L').map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL'.1.fg).map _)
  refine ⟨hsumLat, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL'.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ + b₂, ?_⟩
    rw [pair_hsum]
    push_cast
    linear_combination hb₁ + hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL'.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero] at hb
      exact ⟨b, hb⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add] at hb
      exact ⟨b, hb⟩

end GlobalTheory.Twist.OrthSum

end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.BadShare GlobalTheory.BadShare.Basic
open scoped Classical

namespace GlobalTheory.GLq.SqSeries

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem wh_one_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  unfold wh tr
  rw [Fintype.sum_subsingleton _ 1, eU, coeff_eDat, mul_one]
  have hU : ∀ u : Gn g 0, IsUniUp u.val := fun u a => a.elim0
  have hc : Nat.card {u : GG g 0 // IsUniUp u.val} = 1 := by
    haveI : Nonempty {u : GG g 0 // IsUniUp u.val} := ⟨⟨1, hU 1⟩⟩
    exact Nat.card_unique
  unfold eps
  rw [if_pos (hU 1), hc]
  simp

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (χ : Gn g n → ℂ) :
    wh ψ (fun x => c * χ x) = c * wh ψ χ := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g))
    (h : ∀ p ∈ L, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    wh ψ (hcL L (degL L)) = 1 := by
  induction L with
  | nil => exact wh_one_zero ψ
  | cons p L ih =>
    have hp := h p List.mem_cons_self
    have hL := fun q hq => h q (List.mem_cons_of_mem p hq)
    have hch : ∀ q : Pc g, IsCusp q.2 → IsChar q.2 := fun q hq => by
      obtain ⟨V, -, hV⟩ := hq.2.1
      exact ⟨V, hV⟩
    have c1 := isClass_of_isChar (hch p hp.1)
    have c2 := isClass_of_isChar (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L _ rfl fun q hq => hch q (hL q hq).1).1
    rw [hcL_cons, hc, GlobalTheory.T.whittakerDimension_harishChandraInduction_mul g ψ hψ p.1 (degL L) _ (by simp [degL]) _
      (fun y a b => by simp only [c1 a b]) (fun x a b => by simp only [c2 a b])]
    simp only [wh_const_mul, ih hL, mul_one]
    exact GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ hp.1 hp.2

theorem isGeneric_of_wh (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {n : ℕ} (hn : 0 < n) (V : FDRep ℂ (GG g n))
    (h : wh ψ V.character ≠ 0) : IsGeneric V.ρ := by
  have hk : 0 + 0 < n := hn
  refine ⟨levOfChar ψ hψ n false 0 0 hk, rfl, ?_⟩
  have h1 : op V.ρ (levOfChar ψ hψ n false 0 0 hk).e ≠ 0 := by
    intro h0
    apply h
    have := congrArg (LinearMap.trace ℂ V) h0

    rw [map_zero, op, map_sum] at this
    rw [← this]
    unfold wh tr
    refine Finset.sum_congr (by congr) fun x _ => ?_
    rw [coeff_eU ψ hψ 0 0 hk, map_smul, smul_eq_mul]
    rfl
  obtain ⟨y, hy⟩ : ∃ y, op V.ρ (levOfChar ψ hψ n false 0 0 hk).e y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h1 (LinearMap.ext hc)
  refine ⟨_, hy, fun u hu => ?_⟩
  exact (GlobalTheory.BadShare.EpsProj.mem_range_iff V.ρ (mem_one _) (fun _ _ => mem_mul _) (chi_one _) (fun _ _ => chi_mul _) _).1
    ⟨y, rfl⟩ u ⟨hu, fun hs => absurd hs (by simp [levOfChar])⟩

theorem deg_hcL (L : List (Pc g)) (n : ℕ) (hn : n = degL L)
    (h : ∀ p ∈ L, 0 < p.1 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    hcL L n 1 * (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod = ∏ i ∈ Finset.range n, ((g : ℂ) ^ (i + 1) - 1) := by
  have H := GlobalTheory.T.harishChandraProductList_degree g L n hn
  have e1 : (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod =
      (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod * (L.map fun p => p.2 1).prod := by
    rw [← List.prod_map_mul]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [(h p hp).2, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (h p hp).1, mul_comm]
  have e2 : (L.map fun p => p.2 1).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    rw [(h p hp).2, Finset.prod_eq_zero_iff] at h1
    obtain ⟨i, hi, h2⟩ := h1
    have h3 : g ^ i = 1 := by exact_mod_cast sub_eq_zero.1 h2
    have h4 := (Fact.out : g.Prime).one_lt
    have h5 := (Finset.mem_Ico.1 hi).1
    have := Nat.one_lt_pow (n := i) (by omega) h4
    omega
  rw [e1, ← mul_assoc] at H
  rw [mul_right_cancel₀ e2 H, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem exists_series : GlobalTheory.GLq.Green → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (n : ℕ), 5 ≤ g → 0 < n → ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g n → ℂ, GlobalTheory.BadShare.IsSeries τ ∧ ∀ f ∈ GlobalTheory.BadShare.sqSet g n, ∀ x, (GlobalTheory.GLq.eSerC L n f).coeff x = GlobalTheory.BadShare.zc (τ f) x := by
  intro hG g _ L n hg hn
  obtain ⟨H1, -, H3⟩ := GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG n
  have H4 := fun (f : (ZMod g)[X]) (hf : f ∈ sqSet g n) =>
    H3 f (mem_sqSet.1 hf).1 (mem_sqSet.1 hf).2.1 (mem_sqSet.1 hf).2.2.2 (mem_sqSet.1 hf).2.2.1
  choose! Q Q1 Q2 Q3 Q4 using H4
  have hmem : ∀ f ∈ sqSet g n, IsIrr (hcL ((Q f).map Prod.snd) n) ∧ HasLabel L (hcL ((Q f).map Prod.snd) n) f := by
    intro f hf
    have : hcL ((Q f).map Prod.snd) n ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} := by
      rw [Q4 f hf]; rfl
    exact this
  refine ⟨fun f => hcL ((Q f).map Prod.snd) n, ⟨fun f hf f' hf' h => ?_, fun f hf => ?_⟩, fun f hf x => ?_⟩
  · have a := hmem f hf
    have b := (hmem f' hf').2
    have h' : hcL ((Q f).map Prod.snd) n = hcL ((Q f').map Prod.snd) n := h
    rw [← h'] at b
    exact (H1 _ a.1).unique a.2 b
  · obtain ⟨V, hs, hV⟩ := (hmem f hf).1
    have hV' : V.character = hcL ((Q f).map Prod.snd) n := funext hV
    have hc : ∀ p ∈ (Q f).map Prod.snd, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨(Q1 f hf q hq).1.2.1, (Q1 f hf q hq).2⟩
    refine ⟨V, hs, hV', ?_, ?_⟩
    · have hψ := (levStandard g n false 0 0 hn).hψ
      refine isGeneric_of_wh _ hψ hn V ?_
      have h1 := wh_hcL _ hψ _ hc
      rw [Q3 f hf] at h1
      rw [hV', h1]
      exact one_ne_zero
    · have h1 := deg_hcL _ n (Q3 f hf).symm fun p hp => ⟨(hc p hp).1.1, (hc p hp).2⟩
      have hpos : ∀ i, 1 ≤ g ^ i := fun i => Nat.one_le_pow _ _ (by omega)
      have h2 : (torusCard g f : ℂ) = (((Q f).map Prod.snd).map fun p => ((g : ℂ) ^ p.1 - 1)).prod := by
        rw [torusCard, degType, ← Q2 f hf]
        simp only [Multiset.map_coe, Multiset.prod_coe, List.map_map, Nat.cast_list_prod]
        congr 1
        refine List.map_congr_left fun q hq => ?_
        simp only [Function.comp]
        rw [(Q1 f hf q hq).1.1.2.2.2, Nat.cast_sub (hpos _)]
        simp
      rw [← hV', FDRep.char_one, ← h2] at h1
      apply Nat.cast_injective (R := ℂ)
      rw [Nat.cast_mul, h1, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (hpos _)]
      simp
  · rw [eSerC, Q4 f hf, finsum_mem_singleton]
    exact coeff_alg (zc _) x

end GlobalTheory.GLq.SqSeries
end

section

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal ENNReal Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Height

variable {D : D7} (V : HSp D)

theorem isCompact_setOf_height_le (C : ℝ) : IsCompact {g : GA D V | height V g ≤ C} := by
  refine (GlobalTheory.AdelicU.isCompact_height_le (F := D.host.F) D.sp.cm.sig V.gram C.toNNReal).of_isClosed_subset
    (isClosed_le (continuous_height V) continuous_const) fun g hg => ?_
  exact NNReal.le_toNNReal_of_coe_le hg

variable {X : Type} [NormedAddCommGroup X]

end Height

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] {R : Subgroup G} {μR : Measure R} {μG : Measure G} [SFinite μG]
  [μG.IsMulLeftInvariant] [μR.IsHaarMeasure] [μR.IsInvInvariant]

end Quot

theorem quotientIntegral_trivial_count {G : Type} [Group G] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (f : G → ℂ) : IsQuotIntL1 (R := ⊥) (Measure.dirac 1) Measure.count f (∑ g, f g) := by
  rw [isQuotIntL1_bot]
  refine ⟨Integrable.of_finite, ?_⟩
  rw [integral_fintype]
  · simp
  · exact Integrable.of_finite

end GlobalTheory.Grow
end
end
