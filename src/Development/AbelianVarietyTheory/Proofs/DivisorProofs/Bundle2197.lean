module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle092
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_free_of_definite_form_of_rank_le :
    ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  intro H _ Q hQ hpos hdef r hr
  classical
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have htf : ∀ (k : ℤ) (f : H), k ≠ 0 → k • f = 0 → f = 0 := by
    intro k f hk hkf
    apply hdef
    have h1 := parallelogram_zsmul Q hQ k f
    rw [hkf, h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero 2 hk)
  let P : ℕ → Prop := fun n => ∃ u : Fin n → H, LinearIndependent ℤ u
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest P r := ⟨_, rfl⟩
  have hPn : P n := hn ▸
    Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le r) ⟨Fin.elim0, linearIndependent_empty_type⟩
  obtain ⟨u, hu⟩ := hPn
  have hmax : ¬ P (n + 1) := by
    rintro ⟨v, hv⟩
    have hlt : Nat.findGreatest P r < n + 1 := by omega
    exact Nat.findGreatest_is_greatest (P := P) (n := r) hlt (hr _ v hv) ⟨v, hv⟩
  have hspan : ∀ h : H, ∃ k : ℕ, 0 < k ∧ ∃ m : Fin n → ℤ, k • h = ∑ i, m i • u i := by
    intro h
    by_contra hne
    push_neg at hne
    apply hmax
    refine ⟨Fin.cons h u, LinearIndependent.finCons' h u hu fun c y hy hcy => ?_⟩
    by_contra hc
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
    have hpos' : 0 < c.natAbs := Int.natAbs_pos.2 hc
    rcases Int.natAbs_eq c with hc' | hc'
    · apply hne c.natAbs hpos' (fun i => - m i)
      rw [← natCast_zsmul, ← hc']
      simp only [neg_smul, Finset.sum_neg_distrib, hm]
      exact eq_neg_of_add_eq_zero_left hcy
    · apply hne c.natAbs hpos' m
      rw [← natCast_zsmul, hm]
      have : c • h = - ((c.natAbs : ℤ) • h) := by
        conv_lhs => rw [hc']
        rw [neg_smul]
      rw [this] at hcy
      exact (neg_add_eq_zero.mp hcy)
  obtain ⟨e, he, hdiv⟩ := exists_dvd_coords_of_definite_form H ⊤ Q hQ hpos
    (fun f _ => hdef f) n u (fun _ => trivial) hu
  have hmem : ∀ h : H, (e : ℤ) • h ∈ Submodule.span ℤ (Set.range u) := by
    intro h
    obtain ⟨k, hk, m, hkm⟩ := hspan h
    have hd := hdiv k m h trivial hkm
    choose m' hm' using hd
    have hz : (k : ℤ) • ((e : ℤ) • h - ∑ i, m' i • u i) = 0 := by
      rw [smul_sub, smul_comm (k : ℤ) (e : ℤ) h, natCast_zsmul h k, hkm, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_smul, smul_smul, ← hm' i, sub_self]
    have := htf k _ (by exact_mod_cast hk.ne') hz
    rw [sub_eq_zero.mp this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : H →ₗ[ℤ] Submodule.span ℤ (Set.range u) :=
    LinearMap.codRestrict _ ((e : ℤ) • LinearMap.id) hmem
  have hinj : Function.Injective f := by
    intro a b hab
    have h' : (e : ℤ) • a = (e : ℤ) • b := congrArg Subtype.val hab
    have : (e : ℤ) • (a - b) = 0 := by rw [smul_sub, h', sub_self]
    exact sub_eq_zero.mp (htf e _ (by exact_mod_cast he.ne') this)
  have : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range u)
  have hfin : Module.Finite ℤ H := Module.Finite.of_injective f hinj
  have : Module.IsTorsionFree ℤ H := Module.IsTorsionFree.of_smul_eq_zero fun k x hkx => by
    by_cases hk : k = 0
    · exact Or.inl hk
    · exact Or.inr (htf k x hk hkx)
  have hfree : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
  refine ⟨hfin, hfree, ?_⟩
  exact hr _ _ (Module.finBasis ℤ H).linearIndependent

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_smoothOfRelativeDimension_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (X : Over (Sp K)) [GrpObj X], IsAbelianScheme X →
      ∃ g : ℕ, SmoothOfRelativeDimension g X.hom := by
  intro K _ X _ hX
  haveI := hX.smooth
  haveI := hX.geomConnected
  haveI : ConnectedSpace X.left := GeometricallyConnected.connectedSpace X.hom X.hom.isOpenMap
  obtain ⟨x₀⟩ := (inferInstance : ConnectedSpace X.left).toNonempty
  exact exists_dim_of_preconnected X.hom x₀

end GlobalTheory.AV
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem finrank_torusExtension_le : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ), SmoothOfRelativeDimension g G.hom → (letI := E.addCommGroup; Module.finrank ℤ E.X) ≤ g := by
  intro k _ G _ E g hG
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsSeparated E.B.hom := E.isAbelian.proper.toIsSeparated
  have hη : IsClosedImmersion (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) E.B.hom _ (Over.w _)
  have hpb : IsPullback E.i.left (toUnit (splitTorus (Sp k) E.X)).left E.q.left (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left :=
    E.isKernel.map (Over.forget _)
  have hi : IsClosedImmersion E.i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
  have pt : Sp k := Classical.choice inferInstance
  have hne : Nonempty (splitTorus (Sp k) E.X).left :=
    ⟨(η : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) E.X).left ((toUnit (Over.mk (𝟙 (Sp k)))).left pt)⟩
  exact relDim_le_of_isClosedImmersion k _ G E.i hi hne g _ hG (ReciprocityTheory.ChartRestriction.G.H1.torus_dim (Sp k) E.X)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_relativeDimension_abelianVariety_field : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.AbVarRelDim.exists_relDim | exact GlobalTheory.AbVarRelDim.exists_relDim | (intros; apply GlobalTheory.AbVarRelDim.exists_relDim <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistGen

theorem whisker_eq_twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem mem_of_isPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε))
    (hs : IsPullSecLC L φ ε h s s') (y : Y') (hy : y ∈ nonzeroLocus s') : h y ∈ nonzeroLocus s := by
  obtain ⟨(j : K → L.ι), hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  rw [hs j] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (Scheme.preimage_basicOpen h (s.f j)).ge hj.2⟩

theorem transfer {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (α : D.X)
    (s : LB.Sec (twistLB D.P.A D.P.L 2 (D.c α)))
    (z : (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (hz : z ∈ nonzeroLocus s) :
    ∃ σ : D.SecB 2 α, (snd _ D.P.A).left z ∈ nonzeroLocus σ := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  let A := D.P.A
  let iota : A.left ⟶ (T ⊗ A).left := (lift (toUnit A) (𝟙 A)).left
  have hsec : snd T A ≫ lift (toUnit A) (𝟙 A) = 𝟙 (T ⊗ A) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact (toUnit_unique _ _)
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hiota : iota ((snd T A).left z) = z := by
    have e : (snd T A).left ≫ iota = 𝟙 _ := by rw [← Over.comp_left, hsec]; rfl
    have e' := congrArg (fun f => f.base z) e
    exact e'
  obtain ⟨u₀, hu₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) ![-1, 1]
  let u := LB.pullGen D.P.L _ _ u₀ (toUnit A).left
  have hu : u.IsGen := DVR.pullGen_isGen_of_isGen _ _ u₀ hu₀ _
  let s₁ := pullMulSec s iota u hu
  have hF : FormEq (Sum.elim (fun k => iota ≫ ![(snd T A).left, (translPt A (D.c α)).left] k)
      (fun k => (toUnit A).left ≫ (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) k))
      (Sum.elim ![((2 : ℕ) : ℤ) - 1, 1] ![-1, 1]) (D.famφB α) (DegPre.famε 2) := by
    have e₁ : iota ≫ (snd T A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd]; rfl
    have e₂ : iota ≫ (translPt A (D.c α)).left = (padd A (𝟙 A) (toUnit A ≫ D.c α)).left := by
      rw [← Over.comp_left]
      congr 1
      show lift (toUnit A) (𝟙 A) ≫ ((fst T A ≫ D.c α) * snd T A) = 𝟙 A * (toUnit A ≫ D.c α)
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, lift_snd, ← Category.assoc, lift_fst]
      show (toUnit A ≫ D.c α) * 𝟙 A = 𝟙 A * (toUnit A ≫ D.c α)
      exact mul_comm _ _
    intro U _ hh
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
      DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e₁, e₂]
    simp only [_root_.mul_assoc]; rfl
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hF s₁
  refine ⟨σ, ?_⟩
  set xx := (snd T A).left z
  choose J hJ using fun χ : A.left ⟶ A.left => exists_chart D.P.isLB (χ xx)
  obtain ⟨(k : Fin 2 → D.P.L.ι), hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hv : IsUnit (sval s (𝟙 A.left ≫ iota) xx J) := by
    refine H1.SectionArithmetic.isUnit_sval s (𝟙 A.left ≫ iota) xx hJ k ?_
    rw [Category.id_comp, hiota]; exact hk
  have hval : IsUnit (sval σ (𝟙 A.left) xx J) := by
    rw [hσ _ _ xx J hJ, sval_pullMulSec s iota u hu (𝟙 A.left) xx hJ]
    exact hv.mul (Units.isUnit _)
  have hm := (Good.mem hJ (D.famφB α) (𝟙 A.left))
  rw [sval] at hval
  erw [gs_eq (𝟙 A.left) xx _ hm] at hval
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => J (𝟙 A.left ≫ D.famφB α k), ?_⟩
  exact (A.left.mem_basicOpen _ xx hm).2 hval

theorem exists_sec_nonzeroLocus_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left),
    D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  intro R _ _ _ _ _ D α x hx
  let S := Spec (CommRingCat.of R)
  let tk : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let T : Over S := 𝟙_ (Over S)
  let ρ : Over.mk (tk ≫ T.hom) ⟶ Over.mk T.hom := Over.homMk tk rfl
  obtain ⟨y, hy⟩ : ∃ y : (Over.mk (tk ≫ T.hom) ⊗ D.P.A).left, (snd _ D.P.A).left y = x := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := inferInstance
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := tk ≫ T.hom) (g := D.P.A.hom) p x (by
      rw [hx]; exact IsLocalRing.PrimeSpectrum.comap_residue R p)
    exact ⟨z, hz⟩
  have hg := GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing S D.P _ (tk ≫ T.hom) (ρ ≫ D.c α) y
  rw [← whisker_eq_twistLB] at hg
  obtain ⟨sb, hsb⟩ := hg
  obtain ⟨s, hs⟩ := (GlobalTheory.abelianSchemeLaws_all.2.secTwist S D.P 2 (by norm_num) R T.hom (D.c α)).2 sb
  have hz := mem_of_isPullSecLC D.P.L _ _ _ s sb hs y hsb
  obtain ⟨σ, hσ⟩ := transfer D α s _ hz
  refine ⟨σ, ?_⟩
  have e : (snd T D.P.A).left ((ρ ▷ D.P.A).left y) = x := by
    rw [← hy]
    have e' := congrArg (fun f => f.left.base y) (whiskerRight_snd ρ D.P.A)
    exact e'
  rwa [e] at hσ

end GlobalTheory.TwistGen
end
end
