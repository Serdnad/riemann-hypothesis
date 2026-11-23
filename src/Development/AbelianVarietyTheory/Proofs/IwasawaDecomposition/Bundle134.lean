module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDataLevelFormsTransportFieldMap
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
open Polynomial

namespace GlobalTheory.CuspRep

theorem exists_multiset_qdet {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ M)
    (s : ℂ) (φ : M) (f : M →ₗ[ℂ] ℂ) (hf : f φ = 1) :
    ∃ m : Multiset ℂ, Multiset.card m = n ∧ ∀ u, f (Formalism.REAL.qdet F (u + s) φ) = (m.map (u + ·)).prod := by
  classical
  let Q : Finset (Fin n) → ℂ[X] := fun S => ∏ k ∈ Sᶜ, (X - C ((k : ℂ) - s))
  have hQm : ∀ S, (Q S).Monic := fun S => monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hQd : ∀ S, (Q S).natDegree = Sᶜ.card := fun S => by
    simp only [Q]
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  let R : ℂ[X] := ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S
  have h0 : (Q ∅).degree = n := by
    rw [degree_eq_natDegree (hQm _).ne_zero, hQd]; simp
  have hR : R.degree < (Q ∅).degree := by
    rw [h0]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun S hS => ?_)
    refine degree_le_natDegree.trans_lt ?_
    have h1 : (C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S).natDegree < n := by
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [hQd, Finset.card_compl, Fintype.card_fin]
      have h2 := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS))
      have h3 : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    exact_mod_cast h1
  have hm : (Q ∅ + R).Monic := (hQm _).add_of_left hR
  have hd : (Q ∅ + R).natDegree = n := by
    rw [natDegree_eq_of_degree_eq_some ((degree_add_eq_left_of_degree_lt hR).trans h0)]
  have hc : Multiset.card (Q ∅ + R).roots = (Q ∅ + R).natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨(Q ∅ + R).roots.map Neg.neg, by rw [Multiset.card_map, hc, hd], fun u => ?_⟩
  have e := congrArg (eval u) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc)
  have e2 : ((Q ∅ + R).roots.map Neg.neg |>.map (u + ·)).prod = eval u (Q ∅ + R) := by
    rw [← e]
    simp [eval_multiset_prod, Multiset.map_map, sub_eq_add_neg]
  have hQe : ∀ S, eval u (Q S) = ∏ k ∈ Sᶜ, (u + s - (k : ℂ)) := fun S => by
    simp only [Q, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [e2, GlobalTheory.CapelliTop.qdet_expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n))),
    GlobalTheory.CapelliTop.subdet_empty]

  simp only [R, eval_add, eval_finsetSum, eval_mul, eval_C, hQe, LinearMap.add_apply, LinearMap.sum_apply,
  LinearMap.smul_apply, map_add, map_sum, map_smul, Module.End.one_apply, hf, smul_eq_mul, mul_one]
  congr 1
  exact Finset.sum_congr rfl fun S _ => mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem CuspSub.exists_scalar (π : CuspSub E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (π.cusp φ hφ).1.zfin
  have hle : U ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ π.V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem hasInfChar_infChar_of_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o)) → ∀ (π : CG E a) (τ : E →+* ℂ), π.HasInfChar τ (π.infChar τ) := by
  intro E _ _ _ a hc π τ
  suffices h : ∃ m, π.HasInfChar τ m by
    obtain ⟨m, h⟩ := h
    rwa [h.infChar_eq]
  induction π using Quotient.inductionOn with
  | h π =>
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := a) τ) (((a : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (hc τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CuspRep
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisToBdRPlus_injective : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Function.Injective j := by
  first | exact @GlobalTheory.MemLoc.crisP_injective | exact GlobalTheory.MemLoc.crisP_injective | (intros; apply GlobalTheory.MemLoc.crisP_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOnto

theorem exists_finite_quotient_ne_zero {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (M : AddSubgroup X)
    (hM : M ≠ ⊤) : ∃ (F : Type) (_ : AddCommGroup F) (_ : Finite F) (l : X →+ F), l ≠ 0 ∧ ∀ x ∈ M, l x = 0 := by
  have hM' : M.toIntSubmodule ≠ ⊤ := fun h => hM (eq_top_iff.2 fun x _ => by
    have : x ∈ M.toIntSubmodule := h ▸ Submodule.mem_top
    exact this)
  obtain ⟨N, hN, hMN⟩ := (IsCoatomic.eq_top_or_exists_le_coatom M.toIntSubmodule).resolve_left hM'
  haveI : IsSimpleModule ℤ (X ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 this
  haveI : Finite (ℤ ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField)
  haveI : Finite (X ⧸ N) := Finite.of_equiv _ e.toEquiv.symm
  refine ⟨X ⧸ N, inferInstance, inferInstance, N.mkQ.toAddMonoidHom, fun h => hN.1 ?_, fun x hx => ?_⟩
  · refine eq_top_iff.2 fun x _ => (Submodule.Quotient.mk_eq_zero N).1 ?_
    exact DFunLike.congr_fun h x
  · exact (Submodule.Quotient.mk_eq_zero N).2 (hMN hx)

instance isFinite_splitTorus (S : Scheme.{0}) (F : Type) [AddCommGroup F] [Finite F] :
    IsFinite (splitTorus S F).hom := by
  have : IsFinite (splitTorusAff ZU.{0} F).hom := by
    show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} (torusRing ZU.{0} F))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  exact inferInstanceAs (IsFinite (pullback.snd _ _))

end GlobalTheory.TorusOnto

namespace GlobalTheory.TorusOnto

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem restrict_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    Function.Surjective ρ := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ _ hΩ hφ₀ h₀j
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V) 0 ≫ j := by
    haveI : IsSeparated tV.G.hom := tV.semi.separated
    have hjac : maximalIdeal V ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V (maximalIdeal V) hjac (splitTorus (Sp V) F) tV.G _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V ⧸ maximalIdeal V ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V →+* V ⧸ maximalIdeal V ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback tV.G (thick V (maximalIdeal V) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V (maximalIdeal V) e tV.G) t.G (spMap (q.comp ψ))
        (pullback.fst tV.G.hom (thick V (maximalIdeal V) e) ≫ mV.φ) :=
      (he.comp mV.cart).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P _ (q.comp ψ) e ha _ _ hR
    obtain ⟨ρe, hρe⟩ := hfac P'.D.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance

    have hres : ∀ x ∈ maximalIdeal V ^ (e + 1), residue V x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres m₀.cart
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V).comp ψ) x = 0 := fun x hx =>
      h₀ x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus m₀.cart j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he m₀.cart (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres m₀.cart).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha' m₀'.cart :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V) hres) (P.U.gt e) ha ha' hR m₀'.cart ke
        (RingHom.ext fun x => rfl)
        (hφ₀.trans (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst]))
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P _ ((residue V).comp ψ) e ha' t₀.G m₀'.φ m₀'.cart
    obtain ⟨u, hu⟩ := hfac' P.D.toPre.X (GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : P'.D.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : P'.D.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V) F).hom (thick V (maximalIdeal V) e) ≫ _ =
      pullback.fst (splitTorus (Sp V) F).hom (thick V (maximalIdeal V) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.PELUnif.torus P' hβ n') :=
    (GlobalTheory.T.uniformisationTorus_mono_and_factor E H W (maximalIdeal W) t' P' Ω β 0 (GlobalTheory.TorusPart.map_pow_one_eq_zero hβ) tΩ.G n'.φ n'.cart).1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus n.cart) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOnto
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauShift

open GlobalTheory.PsiTauCoordRel GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev cK (ξ : Spec (CommRingCat.of (FractionRing R))) : Rˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom

abbrev kK (ξ : Spec (CommRingCat.of (FractionRing R))) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (kst ξ).toMonoidHom

variable [IsLocalRing R]

theorem coord_val (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    ∃ u : Rˣ, Units.map (kst ξ).toMonoidHom x =
      cK ξ u * val (D.tau a b) (𝟙 (TK R).left) ξ J := by
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 (TK R).left) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]
  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau a b) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (a + b) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc a _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc b _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)
  have vt := GlobalTheory.PeriodBalance.val_tau D ξ hJ a b
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) =
      Units.map (kst ξ).toMonoidHom (genVal (D.tau a b) j h) := Units.ext eT
  refine ⟨c1⁻¹ * c2 * c3 * c4⁻¹ * c5, ?_⟩
  rw [← eT', dT, g4, vt, g1, g2, g3, h5]
  simp only [cU, map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_add (D : DegPre R) (hB : D.TauBimult) (ξ : Spec (CommRingCat.of (FractionRing R))) {J}
    (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (D.tau (a + a') b) (𝟙 (TK R).left) ξ J = cK ξ w *
      (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau a' b) (𝟙 (TK R).left) ξ J) := by
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 (TK R).left)).trans (val_mul hJ _ _ _))
  rw [val_pull (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) hJ D.cub.t (D.pt3 a a' b)] at e
  have hp : 𝟙 (TK R).left ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp] at e
  obtain ⟨w, hw⟩ := val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t (lift (D.c a) (lift (D.c a') (D.c b))).left fun k => by
    show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) k.down).left) ≫ D.P.A.hom = 𝟙 _
    rw [Category.assoc, Over.w, Over.w]; rfl
  refine ⟨w⁻¹, ?_⟩
  have hw' : val D.cub.t (jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left) ξ J = cK ξ w := hw
  rw [← e, map_inv, eq_inv_mul_iff_mul_eq, mul_comm]
  exact congrArg _ hw'.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  intro R _ _ _ D hB a z b k x x' x'' hx hx' hx''
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have hind : ∀ n : ℕ, ∃ w : Rˣ, val (D.tau (a + n • z) b) (𝟙 (TK R).left) ξ J =
      cK ξ w * (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau z b) (𝟙 (TK R).left) ξ J ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, by rw [zero_nsmul, add_zero, map_one, pow_zero, _root_.one_mul, _root_.mul_one]⟩
    | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := val_add D hB ξ hJ hJc (a + n • z) z b
      refine ⟨w' * w, ?_⟩
      rw [succ_nsmul, ← add_assoc, hw', hw, map_mul, pow_succ]
      ac_rfl
  obtain ⟨w, hw⟩ := hind k
  obtain ⟨u1, e1⟩ := coord_val D ξ hJ hJc hx
  obtain ⟨u2, e2⟩ := coord_val D ξ hJ hJc hx'
  obtain ⟨u3, e3⟩ := coord_val D ξ hJ hJc hx''
  refine ⟨u3 * w * u1⁻¹ * (u2⁻¹) ^ k, ?_⟩
  apply Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ)
  show kK ξ x'' = kK ξ _
  replace e1 : kK ξ x = _ := e1
  replace e2 : kK ξ x' = _ := e2
  replace e3 : kK ξ x'' = _ := e3
  have hc : ∀ v : Rˣ, kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom v) =
      cK ξ v := fun v => Units.ext rfl
  have f1 : val (D.tau a b) (𝟙 (TK R).left) ξ J = cK ξ u1⁻¹ * kK ξ x := by
    rw [e1, map_inv, inv_mul_cancel_left]
  have f2 : val (D.tau z b) (𝟙 (TK R).left) ξ J = cK ξ u2⁻¹ * kK ξ x' := by
    rw [e2, map_inv, inv_mul_cancel_left]
  rw [map_mul, hc, map_mul, map_pow, e3, hw, f1, f2]
  simp only [map_mul, map_inv, map_pow, mul_pow]
  ac_rfl

end GlobalTheory.TauShift
end
end

section

noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.Mem.R3.DefLatBC
open scoped Matrix

theorem tl_bcF_of_blockBCAt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  intro K K' _ _ _ _ _ _ G G' _ _ _ _ Pl0 Pl0' φ hφ e B B' ℓ ℓ' Z Z' s C _ h
  obtain ⟨hC, hH, hact, hnab, hZ, hX, hP, hψ⟩ := h
  obtain ⟨X', P', ψ'⟩ := ℓ'
  dsimp only at hX hP hψ
  subst hP
  obtain ⟨m, b, F, hF, hI, hb⟩ := DefLatBC.exists_dual_family φ
  have hc : Nat.card (ℓ.P.map e.toMonoidHom) = Nat.card ℓ.P :=
    (Nat.card_congr (ℓ.P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hl := lvlIdem_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.P ℓ.ψ ψ' hψ
  have hg : B'.S.gaMat B'.r (goodAt X' (ℓ.P.map e.toMonoidHom) ψ') * C = C * (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).map φ := by
    unfold goodAt
    rw [(group_action_matrix_hom K' B'.S G' B'.r).2, (group_action_matrix_hom K B.S G B.r).2, Matrix.mul_assoc, hl, ← Matrix.mul_assoc,
      idemOf_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.X X' hX, Matrix.map_mul, Matrix.mul_assoc]
  set ℓ' : Lvl K' G' := ⟨X', ℓ.P.map e.toMonoidHom, ψ'⟩ with hℓ'
  obtain ⟨A0, hA0, hE0⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hl)
  obtain ⟨A1, hA1, hE1⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hg)
  change B'.S.lvlE B'.r ℓ'.P ℓ'.ψ * A0 = C * (B.S.lvlE B.r ℓ.P ℓ.ψ).map φ at hE0
  change B'.vE ℓ' * A1 = C * (B.vE ℓ).map φ at hE1
  have hZ0 : B'.Z0 ℓ' Z' = Submodule.span K' ((fun x : Fin (B.nV ℓ) → K => A1 *ᵥ (fun k => φ (x k))) '' (B.Z0 ℓ Z : Set _)) :=
    comap_baseChange (R := K) (R' := K') φ (fun i => algebraMap (𝓞 K') K' (b i)) F hF (fun i a => ⟨F i a, rfl⟩) hb
      C hC.1 A1 hA1.2 _ _ hE1 _ _ hZ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨Gm, hGm, hE2⟩ := subE_baseChange φ A1 hA1.1 _ _ hZ0
  change B'.zE ℓ' Z' * Gm = A1 * (B.zE ℓ Z).map φ at hE2
  have hvPr : B'.vPr ℓ' * C = A1 * (B.vPr ℓ).map φ := orthPr_baseChange φ hφ C A1 hA1 _ _ hH _ _ hE1
  have hHV : A1ᴴ * B'.HV ℓ' * A1 = (B.HV ℓ).map φ := by
    have h1 := gram_baseChange φ hφ C A1 _ _ hH _ _ hE1
    change A1ᴴ * ((Nat.card (ℓ.P.map e.toMonoidHom) : K')⁻¹ • ((B'.vE ℓ')ᴴ * B'.S.H * B'.vE ℓ')) * A1 =
      ((Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ)).map φ
    rw [Matrix.mul_smul, Matrix.smul_mul, h1, hc]
    generalize (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
  have hPq : B'.Pq ℓ' Z' * A1 = Gm * (B.Pq ℓ Z).map φ := orthPr_baseChange φ hφ A1 Gm hGm _ _ hHV _ _ hE2
  have hlPr : B'.lPr ℓ' Z' * A0 = Gm * (B.lPr ℓ Z).map φ := by
    unfold BlockDat.lPr
    rw [Matrix.mul_assoc, hE0, Matrix.mul_assoc, ← Matrix.mul_assoc (B'.vPr ℓ'), hvPr, Matrix.mul_assoc A1,
      ← Matrix.mul_assoc (B'.Pq ℓ' Z'), hPq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hN : B'.S.lvlNab B'.r ℓ'.P ℓ'.ψ = Submodule.span (𝓞 K')
      ((fun x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K => A0 *ᵥ (fun k => φ (x k))) '' (B.S.lvlNab B.r ℓ.P ℓ.ψ : Set _)) :=
    comap_baseChange (R := 𝓞 K) (R' := 𝓞 K') φ b F hF hI hb
      C hC.1 A0 hA0.2 _ _ hE0 _ _ hnab _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨Gm, hGm, ?_, fun x => ?_⟩
  · unfold BlockDat.Tl matLat
    rw [hN]
    exact map_baseChange φ A0 Gm _ _ hlPr _
  · have hv : B'.vE ℓ' *ᵥ (B'.zE ℓ' Z' *ᵥ (Gm *ᵥ fun k => φ (x k))) =
        C *ᵥ fun k => φ ((B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ x)) k) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hE2, ← Matrix.mul_assoc, hE1,
        Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mulVec_mulVec, map_mulVec', ← Matrix.mulVec_mulVec]
    simp only [BlockDat.toF, bcF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hv]

end GlobalTheory.Mem.R3.LiftLatBC

end
end
