module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle016
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle006
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
public import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.trinv :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → 1 ≤ n → ∀ Z : Set (MonoidAlgebra B F.G₀), (∀ z ∈ Z, u.D.Kills z ∧ F.star O B n z ∈ Z) → ∃ (DE : Det n B (u.D.CHQuot Z)) (T : TrInv B (u.D.CHQuot Z)), DE.IsCH ∧ DE.pull (u.D.toQuot Z) = u.D.toDet ∧ (∀ y, T.st (u.D.toQuot Z y) = u.D.toQuot Z (F.star O B n y)) ∧ ∀ y, T.tr y = DE.tr y := by
  intro l _ F n O _ _ _ _ _ r B _ _ _ u hΦ hn Z hZ
  letI := F.grp
  letI := F.top
  haveI := F.tgrp
  haveI := F.cpt
  haveI := F.tdisc
  haveI : CompactSpace F.G₀ := by
    have hc : IsClosed (F.η.ker : Set F.Γ) := Subgroup.isClosed_of_isOpen _ F.η_open
    exact isCompact_iff_compactSpace.mp hc.isCompact
  obtain ⟨DE, hCH, hpull⟩ := d_quotDet u.D u.cont Z (fun z hz => (hZ z hz).1)
  have hl : ((l : ℕ) : B) ∈ maximalIdeal B := by
    have h1 : ((l : ℕ) : O) ∈ maximalIdeal O := by
      haveI := (IsCoef.char (l := l) (O := O))
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ l
    rw [← map_natCast (algebraMap O B), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp h1) (isUnit_of_map_unit (algebraMap O B) _ hu)
  have hM : Submodule.span B
      ((MonoidHom.mrange (MonoidAlgebra.of B F.G₀) : Submonoid (MonoidAlgebra B F.G₀)) :
        Set (MonoidAlgebra B F.G₀)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    refine MonoidAlgebra.induction_on x ?_ ?_ ?_
    · intro m
      exact Submodule.subset_span ⟨m, rfl⟩
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
    · intro b x hx
      exact Submodule.smul_mem _ b hx
  have hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of B F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n →
      u.D.toDet.lam i (MulOpposite.unop (F.starOp O B n x)) = u.D.toDet.lam i x := by
    rintro _ ⟨g, rfl⟩ i _ _
    rw [(d_toDet u.D _).2.1, (d_toDet u.D _).2.1]
    exact u.P i g
  obtain ⟨hop, hCHs, -⟩ := d_star u.D.toDet (F.starOp O B n) _ hM hlam
  have hstarCH : ∀ z ∈ u.D.CH, F.star O B n z ∈ TwoSidedIdeal.span (u.D.CH ∪ Z) := by
    intro z hz
    have hz' : z ∈ u.D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    have h2 := hCHs z hz'
    rw [d_toDet_CH] at h2
    exact TwoSidedIdeal.span_mono Set.subset_union_left h2
  have hI : ∀ y, y ∈ u.D.chBar Z → F.star O B n y ∈ u.D.chBar Z := by
    unfold GDet.chBar
    refine star_closure F n O B (maximalIdeal B) (u.D.CH ∪ Z) hl ?_
    rintro z (hz | hz)
    · exact hstarCH z hz
    · exact TwoSidedIdeal.subset_span (Or.inr (hZ z hz).2)
  have hq : ∀ a b, u.D.toQuot Z a = u.D.toQuot Z b ↔ a - b ∈ u.D.chBar Z := by
    intro a b
    unfold GDet.toQuot
    exact Iff.trans (RingCon.eq _) (TwoSidedIdeal.rel_iff _ _ _)
  have hsurj : Function.Surjective (u.D.toQuot Z) := RingCon.mkₐ_surjective _
  let ψ : u.D.CHQuot Z →ₐ[B] (u.D.CHQuot Z)ᵐᵒᵖ :=
    RingCon.liftₐ (u.D.chBar Z).ringCon ((AlgHom.op (u.D.toQuot Z)).comp (F.starOp O B n)) (by
      intro a b hab
      rw [TwoSidedIdeal.rel_iff] at hab
      show MulOpposite.op (u.D.toQuot Z (F.star O B n a)) = MulOpposite.op (u.D.toQuot Z (F.star O B n b))
      congr 1
      rw [hq, ← (star_basic F n O B).2.2.2.2.2.1]
      exact hI _ hab)
  have hψ : ∀ y, MulOpposite.unop (ψ (u.D.toQuot Z y)) = u.D.toQuot Z (F.star O B n y) := fun y => rfl
  obtain ⟨t, ht⟩ := (d_tr DE).1 hn
  have htq : ∀ w, DE.tr (u.D.toQuot Z w) = u.D.toDet.tr w := by
    intro w
    show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi w).coeff (n - 1)
    rw [← hpull, (d_pull DE (u.D.toQuot Z)).1 w]
  have hinv : ∀ w, u.D.toDet.chi (F.star O B n w) = u.D.toDet.chi w := by
    intro w
    conv_rhs => rw [← hop]
    rw [(d_pull _ (F.starOp O B n)).1 w]
    exact ((d_op _).1 (F.star O B n w)).symm
  refine ⟨DE,
    { st := { toFun := fun x => MulOpposite.unop (ψ x)
              map_add' := fun x y => by simp
              map_smul' := fun b x => by simp }
      st_mul := fun x y => by simp
      st_st := ?_
      tr := t
      tr_comm := ?_
      tr_st := ?_ }, hCH, hpull, fun y => hψ y, fun y => ht y⟩
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change MulOpposite.unop (ψ (MulOpposite.unop (ψ (u.D.toQuot Z y)))) = u.D.toQuot Z y
    rw [hψ, hψ, (star_basic F n O B).1]
  · intro x y
    rw [ht, ht]
    exact (d_tr DE).2.1 1 x y
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change t (MulOpposite.unop (ψ (u.D.toQuot Z y))) = t (u.D.toQuot Z y)
    rw [hψ, ht, ht, htq, htq]
    show (-1) ^ 1 * (u.D.toDet.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi y).coeff (n - 1)
    rw [hinv]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem lift_eq' {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) C) (z : MonoidAlgebra B G) :
    MonoidAlgebra.lift B _ G ρ z = GDet.repAlg ρ C (MonoidAlgebra.mapRingHom G (algebraMap B C) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add (f := _), hf, hg, map_add (f := _), map_add (f := _)]
  | single g b =>
    simp [GDet.repAlg, MonoidAlgebra.lift_single, algebraMap_smul]

theorem UpperTheory.V.Pa.rep_quot :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∃ ρ : u.D.CHQuot P.gens →+* Matrix (Fin n) (Fin n) x.A, ∀ y, ρ (u.D.toQuot P.gens y) = P.rep y := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P
  letI : Algebra B x.A := P.f.toRingHom.toAlgebra
  haveI : CompactSpace G.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.η_open).isCompact
  have hp : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have h1 : maximalIdeal B ≤ Ideal.comap (algebraMap B x.A) (maximalIdeal x.A) := by
    intro b hb
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    haveI := (f_surj P).2
    exact (mem_maximalIdeal _).mp hb (isUnit_of_map_unit P.f.toRingHom b hu)
  have h2 : ∀ a b : Fin n, AdicCont (maximalIdeal x.A) fun g ↦ (mat (x.ρ.comp h.p₀)) g a b := by
    intro a b N
    exact (x.cont a b N).comp_continuous hp
  have h3 : u.D.map (algebraMap B x.A) = GDet.ofRep (mat (x.ρ.comp h.p₀)) := P.maps.1
  have h4 : ∀ z ∈ P.gens,
      MonoidAlgebra.lift B (Matrix (Fin n) (Fin n) x.A) G.G₀ (mat (x.ρ.comp h.p₀)) z = 0 := by
    intro z hz
    rw [lift_eq']
    exact rep_gens P z hz
  obtain ⟨ρ, hρ⟩ := f_rep (maximalIdeal x.A) u.D (mat (x.ρ.comp h.p₀)) P.gens h1 h2 h3 h4
  refine ⟨ρ.toRingHom, fun y => ?_⟩
  have hext : ρ.comp (u.D.toQuot P.gens) = MonoidAlgebra.lift B _ G.G₀ (mat (x.ρ.comp h.p₀)) :=
    MonoidAlgebra.algHom_ext (fun g => by simp [hρ]) (Subsingleton.elim _ _)
  have hy := congrArg (fun φ => φ y) hext
  simp only [AlgHom.comp_apply] at hy
  change ρ (u.D.toQuot P.gens y) = _
  rw [hy, lift_eq']
  rfl
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.urep_of :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), CompleteOrthogonalIdempotents ep → (∀ i, H.DE.D Bh[X] (1 + X ⊗ₜ ep i) = 1 + X) → Nonempty (URep h x D I Bh (algebraMap Bh (FractionRing x.A)) e) := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g hep hD
  letI : CommRing g.AA := g.ring
  letI : Algebra Bh g.AA := g.alg
  letI : Ring H.E := H.ring
  letI : Algebra Bh H.E := H.alg
  letI : Algebra B H.E := H.algB
  haveI : IsScalarTower B Bh H.E := H.tower
  letI algB : Algebra B g.AA := ((algebraMap Bh g.AA).comp (algebraMap B Bh)).toAlgebra
  haveI tower : IsScalarTower B Bh g.AA := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let vr : G.G₀ →* Matrix (Fin n) (Fin n) g.AA :=
    ((g.φ.toRingHom.comp H.ι.toRingHom).toMonoidHom).comp (MonoidAlgebra.of Bh G.G₀)
  have hvr : ∀ γ, vr γ = g.φ (H.ι (MonoidAlgebra.single γ 1)) := fun _ => rfl
  have key : ∀ w, GDet.repAlg vr g.AA (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA) w) =
      g.φ (H.ι (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh) w)) := by
    intro w
    have hext : ((GDet.repAlg vr g.AA).toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA))) =
        (g.φ.toRingHom.comp (H.ι.toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh)))) := by
      apply MonoidAlgebra.ringHom_ext
      · intro b
        have hs : MonoidAlgebra.single (1 : G.G₀) (algebraMap B Bh b) =
            (algebraMap B Bh b) • (1 : MonoidAlgebra Bh G.G₀) := by
          rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
        simp only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one, hs, map_smul]
        exact algebraMap_smul g.AA ((algebraMap B Bh) b) (1 : Matrix (Fin n) (Fin n) g.AA)
      · intro a
        simp only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one]
        rw [one_smul]
        show (algebraMap g.AA g.AA).mapMatrix (vr a) = _
        rw [Algebra.algebraMap_self, RingHom.mapMatrix_id]
        rfl
    exact congrArg (fun f => f w) hext
  let f := g.φ.toLinearMap.restrictScalars B
  refine ⟨{
    AA := g.AA
    ring := g.ring
    alg := g.alg
    algB := algB
    tower := tower
    fin := g.fin
    inj := g.inj
    N := g.N
    compl := g.compl
    mul_mem := g.mul_mem
    typeI := g.typeI
    vr := vr
    span := ?_
    det := gr_det H g hep hD vr hvr
    form := ?_
    red := ?_
    kills := ?_
    thick := gr_thick H g
    P := Submodule.map f H.P
    ker_le_span_sub_sup_map := H.ker_le_span_sub_sup_map.map f
    vr_mem := fun γ => Submodule.mem_map_of_mem (H.mem γ)
    cont := ?_ }⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      exact (g.range _).mp ⟨_, rfl⟩
    · intro Y hY
      obtain ⟨y, rfl⟩ := (g.range Y).mpr hY
      obtain ⟨z, rfl⟩ := H.surj y
      clear hY
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]
        exact Submodule.add_mem _ ha hb
      | single γ c =>
        have hc : (MonoidAlgebra.single γ c : MonoidAlgebra Bh G.G₀) = c • MonoidAlgebra.single γ 1 := by
          rw [MonoidAlgebra.smul_single', mul_one]
        rw [hc, map_smul, map_smul]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨γ, rfl⟩)
  · intro γ
    have h1 : (vr γ)ᵀ = (algebraMap B Bh ↑(e γ ^ (1 - (n : ℤ)))) • vr (G.frame.conj γ)⁻¹ := by
      rw [hvr, ← g.st, H.st, map_smul]
      rfl
    rw [h1, smul_mul_assoc, ← map_mul, inv_mul_cancel, map_one, ← algebraMap_smul g.AA]
    rfl
  · intro γ i j b hb
    have := g.red (H.ι (MonoidAlgebra.single γ 1)) i j b hb
    rw [H.r_ι, Matrix.map_apply] at this
    exact this
  · intro z hz
    rw [key, (H.ker _).mpr (TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩), map_zero]
  · intro j
    obtain ⟨V, hV⟩ := H.cont j
    refine ⟨V, fun γ v hv => ?_⟩
    rw [← Submodule.map_smul'']
    have hm := Submodule.mem_map_of_mem (f := f) (hV γ v hv)
    rw [map_sub] at hm
    exact hm
end
