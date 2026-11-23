module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3421
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

private theorem isFilLift_of_graphFil {k : Type} [Field k]
    {A₀ : Over (Sp k)} [GrpObj A₀] {A : Over (Sp (DualNumber k))} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (GlobalTheory.DeRham.epsRed k) i)
    (hA₀ : IsAbelianScheme A₀) (f : HdR A₀ →ₗ[k] HdR A₀)
    (hE : liftFil (epsDP k) h = graphFil A₀ f)
    (x : HdR A₀) (hx : x ∈ Fil A₀) : IsFilLift h x (f x) := by
  obtain ⟨d, hd⟩ := @exists_crys k _ A₀ _ hA₀ x (f x)
  have hGraph := (@mem_graphFil k _ A₀ _ f d).2
    ⟨x, hx, 0, zero_mem _, fun c => by simpa only [LinearMap.zero_apply, add_zero] using hd c⟩
  exact ⟨d, hE.symm ▸ hGraph, hd⟩

-- Keep the divided powers abstract so the dual-number graph lemmas can supply the hypotheses directly.
private theorem lift_with_filtration
    (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p)
    (C k : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k]
    (π : C →+* k) (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C)
    (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR))
    (κ : DividedPowers (RingHom.ker π)) (hκ : κ = divided₂ hsq)
    (E : Submodule C (Crys κ (spMap π) o₀.A)) (hCompl : ∃ M, IsCompl E M)
    (hReduction : ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔
      ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (π := π) κ rfl o₀.A).Corr d y)
    (hStable : ∀ (c : D.O) d, d ∈ E →
      (haveI := o₀.act.hom c; push κ (spMap π) (o₀.act.act c) d) ∈ E)
    (hIsotropic : ∀ φ' : LinearMap.BilinForm C (Crys κ (spMap π) o₀.A),
      GlobalTheory.AbDual.IsCorrForm κ (spMap π) o₀.A o₀.A o₀.P φ' →
        ∀ x ∈ E, ∀ y ∈ E, φ' x y = 0)
    (hLie : ∀ d : Crys κ (spMap π) o₀.A,
      (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
        push κ (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - tR b.ρ • d ∈ E →
      ∃ w : Fin D.a → Crys κ (spMap π) o₀.A,
        (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
          push κ (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i))
            - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap π)),
      liftFil κ m'.cart = E := by
  subst κ
  obtain ⟨A, grp, i, h, act, hA, hE, hact⟩ :=
    GlobalTheory.HTDeform.exists_lift_oAct p D R b N C k π hπ hsq tR o₀ E hCompl hReduction hStable
  have hComm : IsCommMonObj A := hA.comm
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C k π hπ hsq tR o₀ A i h
      hA act hact (fun φ' hφ' x hx y hy => hIsotropic φ' hφ' x (hE ▸ hx) y (hE ▸ hy))
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ :=
    GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C k π hπ hsq tR o₀ A i h hA
      act hact hN P φ₂ hP hsq2 hpol
  rw [← hE] at hLie
  let o' : GlobalTheory.UPel.HT.Obj b N (spMap tR) :=
    { A := A
      grp := grp
      comm := hComm
      ab := hA
      act := act
      P := P
      isLB := hP
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hker
      rosati := hros
      lie := GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C k
        π hπ hsq tR o₀ A i h hA act hact hLie
      lieRank := GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift p D R b N C k
        π hπ hsq tR o₀ A i h act hact
      eta := eta
      eta_add := e1
      eta_lin := e2
      eta_ker := e3
      geom := e4 }
  let m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap π) :=
    { φ := i, φ₂ := φ₂, cart := h, sq := hsq2, act := hact, pol := hpol, eta := e5 }
  exact ⟨o', m', hE⟩

theorem realise_core (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p) (k : Type) [Field k] (β : R →+* k)
    (s : Sp k ⟶ Sp R) (hs : s = spMap β) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ : LinearMap.BilinForm k (HdR o₀.A)) (hφ : GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ)
    (f : HdR o₀.A →ₗ[k] HdR o₀.A)
    (hf : IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f)
    (tR : R →+* DualNumber k) (htR : tR = (algebraMap k (DualNumber k)).comp β)
    (hs' : s = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap tR) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  subst tR
  subst hs'
  let tR := (algebraMap k (DualNumber k)).comp β
  have hZ := GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration p D R b N k β _ hs o₀
  have : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  have : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k (DualNumber k)
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have hA₀ := o₀.ab
  have hCompl := @GlobalTheory.T.dualNumberGraphFiltration_exists_isCompl k _ o₀.A o₀.grp hA₀ f
  have hReduction := @GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction k _ o₀.A o₀.grp hA₀ f
  have hStable (c : D.O) := @GlobalTheory.T.dualNumberGraphFiltration_pushforward_mem
    k _ o₀.A o₀.grp (o₀.act.act c) (o₀.act.hom c) f (hf.1 c)
  have hIsotropic := @GlobalTheory.T.dualNumberGraphFiltration_isotropic_of_skew
    k _ o₀.A o₀.grp hA₀ o₀.P o₀.isLB φ hφ f hf.2.2
  have hLie := GlobalTheory.T.dualNumberGraphFiltration_lie_of_map_into_hodge p D R b N k β _ o₀ f hZ hf.2.1
  obtain ⟨o', m', hE⟩ := lift_with_filtration p D R b N hN (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ (SqExt.dual k).sq tR o₀ (epsDP k) rfl (graphFil o₀.A f)
    hCompl hReduction hStable hIsotropic hLie
  exact ⟨o', m', @isFilLift_of_graphFil k _ o₀.A o₀.grp o'.A o'.grp m'.φ m'.cart hA₀ f hE⟩

end GlobalTheory.HTRealise

theorem GlobalTheory.UPel.HT.realise_isKS : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  intro p _ D R _ b N _ hN k _ _ t o₀ β ht φ hφ f hf
  have e1 : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have e2 : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun r => rfl)
  rw [e1]
  exact GlobalTheory.HTRealise.realise_core p D R b N hN k β t ht o₀ φ hφ f hf _ rfl e2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTNecessary

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀] {A' : Over (Sp (DualNumber k))} [GrpObj A']
  {i : A₀.left ⟶ A'.left} {h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i}

theorem isFilLift_add {x y x' y' : HdR A₀} (e : IsFilLift h x y) (e' : IsFilLift h x' y') :
    IsFilLift h (x + x') (y + y') := by
  obtain ⟨d, hd, e⟩ := e
  obtain ⟨d', hd', e'⟩ := e'
  refine ⟨d + d', add_mem hd hd', fun c ↦ ?_⟩
  rw [LinearMap.add_apply, e, e']
  ext <;> simp

theorem isFilLift_smul {x y : HdR A₀} (e : IsFilLift h x y) (r : k) :
    IsFilLift h (r • x) (r • y) := by
  obtain ⟨d, hd, e⟩ := e
  refine ⟨algebraMap k (DualNumber k) r • d, Submodule.smul_mem _ _ hd, fun c ↦ ?_⟩
  rw [LinearMap.smul_apply, e]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem isFilLift_zero : IsFilLift h (0 : HdR A₀) 0 :=
  ⟨0, zero_mem _, fun c ↦ by
    simp only [LinearMap.zero_apply, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero]⟩

theorem isFilLift_push (f₀ : A₀ ⟶ A₀) (f : A' ⟶ A') [IsMonHom f₀] [IsMonHom f] (e : i ≫ f.left = f₀.left ≫ i)
    {x y : HdR A₀} (hxy : IsFilLift h x y) :
    IsFilLift h (push (dp0 k) (𝟙 _) f₀ x) (push (dp0 k) (𝟙 _) f₀ y) := by
  obtain ⟨d, hd, e'⟩ := hxy
  have hmem := push_mem_liftFil (epsDP k) h h f₀ f e hd
  refine ⟨_, hmem, fun c ↦ ?_⟩
  have k1 : GrpMor (dp0 k) (𝟙 _) A₀ (epsDP k) (DeRham.epsRed k) A₀
      (algebraMap k (DualNumber k)) (𝟙 _) f₀.left :=
    ⟨(constMor A₀).dp, (constMor A₀).base, (homMor (dp0 k) (𝟙 _) f₀).w,
      (homMor (dp0 k) (𝟙 _) f₀).mul⟩
  have e1 := GrpMor.pull_pull (constMor A₀) (homMor (epsDP k) _ f₀) k1 (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f₀) (constMor A₀) k1 (fun _ ↦ rfl) rfl c
  rw [push_apply]
  show d (primPull _ _ f₀ _) = _
  erw [primPull, e1, ← e2, e']
  rfl

theorem exists_isFilLift (hA' : IsAbelianScheme A') {x : HdR A₀} (hx : x ∈ Fil A₀) : ∃ y, IsFilLift h x y := by
  obtain ⟨g, hg⟩ := GlobalTheory.KSGraph.exists_dim A' hA'
  obtain ⟨v, ⟨y, hy, -⟩, -⟩ := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme GlobalTheory.T.abelianScheme_firstDeRham_structure h hA' hg x hx
  exact ⟨y, hy⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ φ hφ o' m'
  have hab₀ := o₀.ab
  have hab' := o'.ab
  have hL1 : ∀ x ∈ Fil o₀.A, ∃ y, IsFilLift m'.cart x y := fun x hx ↦ exists_isFilLift hab' hx
  have hG := GlobalTheory.KSGraph.isFilLift_iff_sub_mem k o₀.A o'.A m'.φ m'.cart hab'
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Fil o₀.A)
  let bs := Module.Basis.ofVectorSpace k (Fil o₀.A)
  let f : Fil o₀.A →ₗ[k] HdR o₀.A := bs.constr k fun j ↦ (hL1 _ (bs j).2).choose
  have hf : ∀ x : Fil o₀.A, IsFilLift m'.cart x.1 (f x) := by
    intro x
    have hx : x ∈ Submodule.span k (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Module.Basis.constr_basis]
      exact (hL1 _ (bs j).2).choose_spec
    | zero => simpa using isFilLift_zero
    | add x y _ _ hx hy => simpa using isFilLift_add hx hy
    | smul r x _ hx => simpa using isFilLift_smul hx r
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := f ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hg : ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := fun x hx ↦ by
    have : Submodule.linearProjOfIsCompl _ _ hC x = ⟨x, hx⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨x, hx⟩
    simpa [g, this] using hf ⟨x, hx⟩
  refine ⟨g, ⟨fun a x hx ↦ ?_, fun z hz ↦ ?_, fun x hx y hy ↦ ?_⟩, hg⟩
  · haveI := o₀.act.hom a
    haveI := o'.act.hom a
    have hax : GlobalTheory.HTCount.crysAct o₀ a x ∈ Fil o₀.A := by
      rw [GlobalTheory.HTCount.crysAct_apply]; exact push_mem_Fil _ hx
    have e1 : IsFilLift m'.cart (GlobalTheory.HTCount.crysAct o₀ a x) (GlobalTheory.HTCount.crysAct o₀ a (g x)) := by
      rw [GlobalTheory.HTCount.crysAct_apply]
      exact isFilLift_push (o₀.act.act a) (o'.act.act a) (m'.act a).symm (hg x hx)
    exact (hG _ hax _ _ e1).1 (hg _ hax)
  · obtain ⟨hz₀, hz⟩ := GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil p D R b N k t o₀ β hβ o' m' z hz
    simpa using (hG _ hz₀ _ _ hz).1 (hg _ hz₀)
  · exact GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew p D R b N k t o₀ φ hφ o' m' x hx y hy _ _ (hg x hx) (hg y hy)

end GlobalTheory.HTNecessary
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

theorem DivOrder.mul_comm_of_eq_int {O : Type} [Ring O] {x y : O} {c : ℤ}
    (htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a))
    (hxy : x * y = (c : O))
    (hy : ∀ y : O, y ≠ 0 → ∃ w : O, ∃ c' : ℤ, c' ≠ 0 ∧ y * w = (c' : O)) :
    y * x = (c : O) := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [mul_zero] at hxy
    rw [zero_mul, hxy]
  obtain ⟨w, c', hc', hyw⟩ := hy y hy0
  have h1 : (c : O) * w = (c' : O) * x := by
    have : x * (y * w) = (x * y) * w := (_root_.mul_assoc _ _ _).symm
    rw [hyw, hxy, ← Int.cast_comm] at this
    exact this.symm
  have h2 : (c' : O) * (y * x) = (c' : O) * (c : O) := by
    calc (c' : O) * (y * x) = y * ((c' : O) * x) := (Int.cast_commute c' y).left_comm x
      _ = y * ((c : O) * w) := by rw [h1]
      _ = (c : O) * (y * w) := ((Int.cast_commute c y).left_comm w).symm
      _ = (c' : O) * (c : O) := by rw [hyw, Int.cast_comm]
  have h3 : c' • (y * x) = c' • (c : O) := by
    simpa [zsmul_eq_mul] using h2
  exact htf c' hc' h3

theorem DivOrder.exists_zsmul_eq_tmul (O : Type) [Ring O] (z : ℚ ⊗[ℤ] O) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x : O, n • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q o =>
    refine ⟨(q.den : ℤ), by exact_mod_cast q.den_nz, q.num • o, ?_⟩
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    congr 1
    rw [zsmul_eq_mul, zsmul_eq_mul, _root_.mul_one]
    push_cast
    exact Rat.den_mul_eq_num q
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨n₁, hn₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, hn₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, n₂ • x₁ + n₁ • x₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, e₁, mul_comm, mul_smul, e₂, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]

theorem DivOrder.isUnit_of_ne_zero (O : Type) [Ring O] [Module.Free ℤ O]
    (hdiv : ∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O))
    (z : ℚ ⊗[ℤ] O) (hz : z ≠ 0) : IsUnit z := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a) := by
    intro n hn a b hab
    apply hinj
    have h' : (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] a) = (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] b) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_smul]
      exact congrArg _ hab
    exact smul_right_injective _ (by exact_mod_cast hn : (n : ℚ) ≠ 0) h'
  obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
  have hx : x ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, ← Int.cast_smul_eq_zsmul ℚ] at e
    exact hz ((smul_eq_zero.mp e).resolve_left (by exact_mod_cast hn))
  obtain ⟨y, c, hc, hxy⟩ := hdiv x hx
  have hyx : y * x = (c : O) := DivOrder.mul_comm_of_eq_int htf hxy hdiv
  set jj : O →ₐ[ℤ] ℚ ⊗[ℤ] O := Algebra.TensorProduct.includeRight with hjj
  have hjx : IsUnit (jj x) := by
    rw [isUnit_iff_exists]
    refine ⟨algebraMap ℚ _ ((c : ℚ)⁻¹) * jj y, ?_, ?_⟩
    · rw [Algebra.left_comm, ← map_mul, hxy, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
    · rw [_root_.mul_assoc, ← map_mul, hyx, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
  have hz' : z = algebraMap ℚ _ ((n : ℚ)⁻¹) * jj x := by
    have : jj x = (1 : ℚ) ⊗ₜ[ℤ] x := rfl
    rw [← Algebra.smul_def, this, ← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  rw [hz']
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hn))).map _).mul hjx

theorem potModel_of_intDivOrder_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → (∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O)) → g < Module.finrank ℤ O → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hsm O _ _ _ act hmon h1 hmul hadd hdiv hg
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have hspan : Submodule.span ℚ (Set.range
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
    have hz : z = ((n : ℚ)⁻¹) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
      rw [← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
        one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hrank : Module.finrank ℚ (ℚ ⊗[ℤ] O) = Module.finrank ℤ O := Module.finrank_baseChange
  exact GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_leftAction V K A g hA hsm O act hmon h1 hmul hadd (ℚ ⊗[ℤ] O)
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom
    (DivOrder.isUnit_of_ne_zero O hdiv) hinj hspan (hrank ▸ hg)

end GlobalTheory
end
