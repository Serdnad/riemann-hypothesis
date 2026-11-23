module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle021
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

namespace GlobalTheory.NatMulMemUnitaryExistence

open NumberField

theorem exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : 𝓞 E, (a : E) = (k : E) * c := by
  obtain ⟨y, hy, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hcast : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  have hint' : IsIntegral ℤ ((y.natAbs : E) * c) := by
    rcases Int.natAbs_eq y with h | h
    · rw [hcast, ← h, ← zsmul_eq_mul]; exact hint
    · have h2 : (y.natAbs : ℤ) = -y := by omega
      rw [hcast, h2, Int.cast_neg, neg_mul, ← zsmul_eq_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  apply PI.WAU.exists_nat_smul_mem <;> assumption

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), ∃ (d : ℕ), (0 : ℕ) < d ∧ d • x ∈ L :=
  fun L hL x => main L hL x

end GlobalTheory.NatMulMemUnitaryExistence
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SmallExtLift

theorem triv_prod_of_small_extension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → Triv (M.pull π) → Triv M := by
  intro R _ _ ε hm A B x₀ y₀ fA fB pA pB hA hB M hM ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ X' π f' P hε ⟨t, ht⟩
  have hεε : ε * ε = 0 := hm ε hε
  have sep : IsSeparated (A ⊗ B).hom := by
    change IsSeparated (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have fl : Flat (A ⊗ B).hom := by
    change Flat (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have : (A ⊗ B).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (A ⊗ B).hom]; infer_instance⟩
  obtain ⟨I, V, j, hj, u, α, hV, haff, hu, H⟩ := exists_lift hεε P hM t ht
  by_cases h0 : ε = 0
  · exact H.gen hεε hM hV hu (fun _ => 0) fun a b x ha hb => by rw [h0, map_zero, zero_mul]
  let φ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let F := Over.pullback φ
  have kA : IsProper (F.obj A).hom := by
    change IsProper (pullback.snd A.hom φ); infer_instance
  have kB : IsProper (F.obj B).hom := by
    change IsProper (pullback.snd B.hom φ); infer_instance
  let i : (F.obj A ⊗ F.obj B).left ⟶ (A ⊗ B).left :=
    (Functor.Monoidal.μIso F A B).hom.left ≫ pullback.fst (A ⊗ B).hom φ
  have Pk : IsPullback i (F.obj A ⊗ F.obj B).hom (A ⊗ B).hom φ := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback (A ⊗ B).hom φ)
      ((Over.forget _).mapIso (Functor.Monoidal.μIso F A B).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · change _ ≫ 𝟙 _ = (Functor.Monoidal.μIso F A B).inv.left ≫ i
      rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
      simp
    · exact (Category.comp_id _).trans (Over.w (Functor.Monoidal.μIso F A B).inv).symm
  have slice : ∀ (C : Over (Sp R)) [Flat C.hom], Function.Bijective
      (pullback.snd C.hom q).appTop.hom → ∀ (s : C ⟶ A ⊗ B) (r : A ⊗ B ⟶ C) [IsSeparated r.left],
      s ≫ r = 𝟙 C →
      ∀ (t : LB.Gen (M.pull s.left)), t.IsGen → ∀ sk : F.obj C ⟶ F.obj A ⊗ F.obj B,
      sk ≫ (Functor.Monoidal.μIso F A B).hom = F.map s → _ := fun C _ hC s r _ hs t ht sk e => by
    have h1 : s.left ≫ r.left = 𝟙 _ := congrArg (fun q => q.left) hs
    have : IsClosedImmersion (s.left ≫ r.left) := by rw [h1]; infer_instance
    have : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left r.left
    have : Flat (s.left ≫ (A ⊗ B).hom) := by rw [Over.w]; infer_instance
    exact H.slice_fibre (i := i) hεε h0 hV haff s.left (π := pullback.fst C.hom q)
      (f' := pullback.snd C.hom q) (by rw [Over.w]; exact IsPullback.of_hasPullback _ _)
      hC.2 hu t ht (iA := pullback.fst C.hom φ)
      (fk := pullback.snd C.hom φ) (by rw [Over.w]; exact pullback.condition) sk.left (by
        rw [← Category.assoc, ← Over.comp_left, e]
        exact pullback.lift_fst _ _ _)
  have one : ∀ (C D : Over (Sp R)) (z : 𝟙_ (Over (Sp R)) ⟶ D),
      toUnit (F.obj C) ≫ Functor.LaxMonoidal.ε F ≫ F.map z = F.map (toUnit C ≫ z) := fun C D z => by
    rw [F.map_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.OplaxMonoidal.η F)]
    exact toUnit_unique _ _
  obtain ⟨ψ, hψ⟩ := GlobalTheory.KuennethOne.kuenneth_injective (IsLocalRing.ResidueField R) (F.obj A)
    (F.obj B) (Functor.LaxMonoidal.ε F ≫ F.map x₀) (Functor.LaxMonoidal.ε F ≫ F.map y₀)
    inferInstance inferInstance inferInstance inferInstance
    (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom φ))
    (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom φ)) I
    (fun a => i ⁻¹ᵁ V a) (by rw [← Scheme.Hom.preimage_iSup, hV]; rfl)
    (fun a b => (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b))
    (fun a b d => gr_ext fun y hy => by
      rw [map_add (f := _), gr_res, gr_res, gr_res, gr_appLE, gr_appLE, gr_appLE]
      exact H.cocycle_fibre hεε h0 hM haff hu Pk.w a b d y hy.1.1 hy.1.2 hy.2)
    (@slice A _ (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom q)) _ (fst A B)
      (by change IsSeparated (pullback.fst A.hom B.hom); infer_instance)
      (by simp) t₁ ht₁ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
    (@slice B _ (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom q)) _ (snd A B)
      (by change IsSeparated (pullback.snd A.hom B.hom); infer_instance)
      (by simp) t₂ ht₂ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
  exact H.gen_fibre hεε hm hM hV haff hu Pk ψ hψ

end GlobalTheory.SmallExtLift
end

section

noncomputable section

namespace GlobalTheory.LevActCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem levelAction_overlap_le_source_chart {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) (x : Sp S ⟶ Xo.X)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      (PPx x).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hz.2

theorem overlap_le_tgt {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) {x x' : Sp S ⟶ Xo.X}
    (pm : Gx x ⟶ Gx x')
    (hp : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ φ)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      pm ⁻¹ᵁ (PPx x').U (fun _ => i) := by
  intro z hz
  have h1 : ((snd (Over.mk x) Xo.univ.t.G).left ≫ φ).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
    Set.mem_iInter.1 hz.1 PUnit.unit
  rw [← hp] at h1
  exact Set.mem_iInter.2 fun _ => h1

end GlobalTheory.LevActCompare
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_isUnit_of_isLocalRing (T : Type) [CommRing T] [IsLocalRing T] :
    ∃ n : ℕ, n.Prime ∧ IsUnit (n : T) := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : T) with h | h
  · exact ⟨3, Nat.prime_three, by simpa using h⟩
  · refine ⟨2, Nat.prime_two, ?_⟩
    have : (1 - 3 : T) = -((2 : ℕ) : T) := by push_cast; ring
    rw [this] at h
    exact (IsUnit.neg_iff _).1 h

theorem existsUnique_hom_extension_semiAbelian_dvr :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) := by
  intro hfin T K _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have := hG.comm
  have := hG'.comm
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have hGflat : Flat G.hom := inferInstance
  obtain ⟨n, hn, hnT⟩ := exists_prime_isUnit_of_isLocalRing T
  let Φ := Over.pullback (spMap (algebraMap T K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ G') := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G G'
  have hi : IsMonHom i := inferInstance
  have hi1 : i ≫ Φ.map (fst G G') = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G G') = f := by simp [i]
  have hs1 : IsSeparated (fst G G').left := inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom))
  have hs2 : LocallyOfFiniteType (fst G G').left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom))
  have hs3 : QuasiCompact (fst G G').left :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom G'.hom))
  have hsP : IsSeparated (G ⊗ G').hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom ≫ G.hom))
  have hlP : LocallyOfFiniteType (G ⊗ G').hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom ≫ G.hom))
  have hs4 : IsSeparated (Φ.map (fst G G')).left := by
    have h1 : IsSeparated (Φ.obj (G ⊗ G')).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ G').hom _))
    rw [← Over.w (Φ.map (fst G G'))] at h1
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have hic : IsClosedImmersion i.left := by
    have h1 : IsClosedImmersion (i.left ≫ (Φ.map (fst G G')).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]; infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G G')).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure T K (G ⊗ G') (Φ.obj G) i hic
  obtain ⟨_, hio', -, hc⟩ := flat_closure_subgroup T K (G ⊗ G') Ga io (Φ.obj G) i e hio hGa hi he
  have := hc inferInstance
  have hp : IsMonHom (io ≫ fst G G') := inferInstance
  have hpK : Φ.map (io ≫ fst G G') = e.hom := by
    rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  have hpKi : IsIso (Φ.map (io ≫ fst G G')) := by rw [hpK]; infer_instance
  have hGaS : IsSeparated Ga.hom := by rw [← Over.w io]; infer_instance
  have hGaL : LocallyOfFiniteType Ga.hom := by rw [← Over.w io]; infer_instance
  have hp1 : IsSeparated (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp2 : LocallyOfFiniteType (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp3 : QuasiCompact (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hnt := KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one T K Ga G (io ≫ fst G G') n hp hGaS
    (etale_mulN_torsion_dvr T Ga n hnT hGa hGaL).2
    (etale_mulN_torsion_dvr T G n hnT hGflat inferInstance).2 hpKi
  have hnS : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hnT.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  have hker := finite_geometric_kernel_of_pow_eq_one hfin (Sp T) G G' Ga io n hG' hio' hio hn hnS hnt
  have hqf := locallyQuasiFinite_of_finite_geometric_ker (Sp T) Ga G (io ≫ fst G G') hp hp2 hp3 hker
  have hiso := isIso_of_quasiFinite_of_isIso_genericFibre_dvr T K Ga G (io ≫ fst G G') hp hGa hp1 hp2
    hp3 hqf hG.smooth hG.geomConnected hpKi
  have hF : Φ.map (inv (io ≫ fst G G') ≫ io ≫ snd G G') = f := by
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, hpK, Functor.map_comp, ← he,
      Category.assoc, hi2]
  refine ⟨inv (io ≫ fst G G') ≫ io ≫ snd G G', ⟨?_, hF⟩, fun F hF' => ?_⟩
  · refine flat_dvr_generic_fibre.2.2 T K G G' _ hGflat hG'.separated ?_
    exact hF ▸ hf
  · exact flat_dvr_generic_fibre.1 T K G G' hGflat hG'.separated _ _ (hF'.2.trans hF.symm)

end GlobalTheory
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin

namespace GlobalTheory.HolLieFrame

theorem differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ} (W : V → Fin g → ℂ)
    (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ →
      DifferentiableAt ℂ (fun b => L b (W b)) b₀ → L b₀ w = 0) → w = 0) : DifferentiableAt ℂ W b₀ := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ ∧
        DifferentiableAt ℂ (fun b => L b (W b)) b₀ ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        exact ⟨fun b => L b + L' b, h1.add h1', h2.add h2', fun w => by simp [h3, h3']⟩
      zero_mem' := ⟨fun _ => 0, differentiableAt_const _, by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        exact ⟨fun b => c • L b, h1.const_smul c, h2.const_smul c, fun w => by simp [h3]⟩ }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : DifferentiableAt ℂ J b₀ :=
    (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b₀
      (differentiableAt_pi.2 h1)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b₀ := differentiableAt_pi.2 h2
  refine ((hJ.inverse hJ0).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJ.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)] with b hb
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b)) (Ring.inverse_mul_cancel _ hb)
  exact this.symm

theorem evalPt_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem exists_fraction {A : Type} [CommRing A] {X : Scheme.{0}} (ψ : Sp A ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (t₀ : A →+* ℂ) (h₀ : ⊤ ≤ (spMap t₀ ≫ ψ) ⁻¹ᵁ U) :
    ∃ r a : A, t₀ r ≠ 0 ∧ ∀ (C : Type) [CommRing C] (t : A →+* C), IsUnit (t r) →
      ∃ h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U, evalPt (spMap t ≫ ψ) U h f * t r = t a := by
  have hY := isAffineOpen_top (Sp A)
  obtain ⟨s, hsU, hs⟩ := hY.exists_basicOpen_le (V := ψ ⁻¹ᵁ U)
    ⟨_, (top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ ψ U).1 h₀)⟩ trivial
  have hloc := hY.isLocalization_basicOpen s
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) ((ψ.appLE U _ hsU).hom f)
  have ha' : (ψ.appLE U _ hsU).hom f * resG _ ((Sp A).basicOpen_le s) (s ^ n) =
    resG _ ((Sp A).basicOpen_le s) a := ha
  obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 s
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 a
  have hs₀ : t₀ s ≠ 0 := by
    have := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem (spMap t₀) _).2 hs)
    rwa [valAt'_eq_evalPt _ _ le_rfl, evalPt_spMap] at this
  refine ⟨s ^ (n + 1), a * s, by rw [map_pow]; exact pow_ne_zero _ hs₀, fun C _ t ht => ?_⟩
  have hu : IsUnit (t s) := by
    rw [map_pow] at ht
    exact (isUnit_pow_iff n.succ_ne_zero).1 ht
  have hD : ⊤ ≤ spMap t ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s) := by
    rw [← evalPt_spMap t s] at hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at hu'
    have := Scheme.basicOpen_appLE (spMap t) ⊤ ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s)
    rw [(Sp C).basicOpen_of_isUnit hu', top_inf_eq] at this
    exact this.le
  have h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U := fun p hp => hsU (hD hp)
  refine ⟨h, ?_⟩
  have := congrArg (evalPt (spMap t) _ hD) ha'
  rw [map_mul, evalPt_appLE _ _ _ _ _ _ _ h, evalPt_res _ _ le_rfl, evalPt_res _ _ le_rfl, map_pow, evalPt_spMap,
    evalPt_spMap] at this
  rw [map_pow, pow_succ, ← _root_.mul_assoc, this, map_mul]

theorem exists_hol_snd {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V) (hev : ∀ c, DifferentiableAt ℂ (fun b => ev b c) b₀)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, DifferentiableAt ℂ F b₀ ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹,
    ((hev a.snd).sub (((hev a.fst).mul ((hev r.fst).inv hr')).mul (hev r.snd))).mul ((hev r.fst).inv hr'), ?_⟩
  filter_upwards [(hev r.fst).continuousAt.eventually_ne hr'] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

theorem differentiableAt_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    {B : Set V} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) (j : Sp R ⟶ X) [IsOpenImmersion j] (ev : V → (R →+* ℂ))
    (h : ∀ b ∈ B, y b = spMap (ev b) ≫ j) {b₀ : V} (hb : b₀ ∈ B) (c : R) :
    DifferentiableAt ℂ (fun b => ev b c) b₀ := by
  have hle : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤) := (j.preimage_image_eq ⊤).ge
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ (j ''ᵁ ⊤) := by
    rw [h b₀ hb]
    exact fun p _ => hle (Set.mem_univ _)
  refine (LocalLift.hol_differentiableAt hy hb h₀
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))).congr_of_eventuallyEq ?_
  filter_upwards [LocalLift.hol_eventually_mem hy hb h₀] with b hb'
  rw [h b hb'.1, ← valAt'_appLE _ j _ ⊤ hle _ le_rfl, valAt'_eq_evalPt _ _ le_rfl, ← evalPt_spMap (ev b) c,
    ← CommRingCat.comp_apply (j.appIso ⊤).inv, Scheme.Hom.appIso_inv_appLE]
  simp

theorem differentiableAt_fderiv {m g : ℕ} {X : Scheme.{0}} {B : Set (Fin m → ℂ)}
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (he : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2)) {b₀ : Fin m → ℂ} (hb : b₀ ∈ B)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ e b₀ 0 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => fderiv ℂ (fun z => valAt' (e b z) U f) 0) b₀ := by
  have h1 := SCV.analyticOnNhd_of_differentiableOn (he U f).1 (he U f).2 (b₀, 0) ⟨⟨hb, trivial⟩, h₀⟩
  have h2 := ContDiffAt.fderiv (𝕜 := ℂ) (f := fun b z => valAt' (e b z) U f) (g := fun _ => 0) (x₀ := b₀) (m := 1)
    (n := 2) h1.contDiffAt contDiffAt_const le_rfl
  exact h2.differentiableAt one_ne_zero

section Fibre

open GlobalTheory.GrpTangent

variable {G : Over (Sp ℂ)} [GrpObj G] {X : Scheme.{0}} {ψ : G.left ⟶ X} {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}

end Fibre

end GlobalTheory.HolLieFrame

namespace GlobalTheory

open HolLieFrame
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

end GlobalTheory
end
end
