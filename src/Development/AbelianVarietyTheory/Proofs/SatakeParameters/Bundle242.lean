module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import GroundTheory.AutomorphicForms.SmoothRep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle105
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.SiteSys

variable {D : D7}

theorem orbMap_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) (s : ZMod (nP D p)) :
    OrbitPlaces.orbMap D p (posPl D p r e) s = OrbitPlaces.orbMap D p r (s + (e : ZMod (nP D p))) := by
  unfold OrbitPlaces.orbMap
  rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p r s.val, posPl_mod, posPl_add, add_comm]

theorem topsOrb_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.topsOrb D p (posPl D p r e) = OrbitPlaces.topsOrb D p r := by
  unfold OrbitPlaces.topsOrb
  refine Finset.card_equiv (Equiv.addRight (e : ZMod (nP D p))) fun s => ?_
  simp [orbMap_posPl]

theorem errF_posPl {L : SizeData₂ D} (K : Consts) (ce : ErrC) (j p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.errF L K ce j p (posPl D p r e) = OrbitPlaces.errF L K ce j p r := by
  have h : ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p (posPl D p r e) s) =
      ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p r s) := by
    simp only [orbMap_posPl]
    exact Equiv.sum_comp (Equiv.addRight (e : ZMod (nP D p))) (fun s => wPl D j (OrbitPlaces.orbMap D p r s))
  unfold OrbitPlaces.errF
  rw [h, topsOrb_posPl]

theorem posPl_true_one {p : ℕ} (hs : ¬ IsSg D p) (t : HH D) : posPl D p (true, t) 1 = (true, t + hP D p) := by
  simp [posPl, partner, hs]

theorem notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

theorem sysTw_sites : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  intro D L hT X Y K Dx lev Xe ce E LC hty hfa hF hadm hSh hCL hS hE μ hμ hT' hty' u w hg hQ
  obtain ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, h0, hj⟩ := hS μ hμ u w hg hQ
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.SecondOrbits.places_off_first_orbits D u w hg L hT X Y hty
  refine ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA,
    fun v j => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, r v) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, r v) else 0,
    ?_, ?_⟩
  · intro v hv j hjm
    obtain ⟨-, -, -, a2c, -, -, -, -, -, -, -, -, a11⟩ := hA
    by_cases hp : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hp]
      exact GlobalTheory.T.local_model_bound_place_over_second_embedding D u w hg L hT X Y K ce E hty hfa hadm hSh hCL hp _ _ std vp unif eO eO_spec dG dG_spec om Y5 a2c v (r v)
        (hr1 v hv).1 (hr1 v hv).2.2 j hjm
    · simp only [if_neg hp]
      exact a11 v j (lt_of_lt_of_eq hjm (hty u w hg).1.symm)
  · refine (GlobalTheory.T.low_term_le_second_real_place_bounds D u w hg L X K ce Xe dG hF h0 hj).trans (sub_le_sub_right (le_of_eq ?_) _)
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (hr2 (fun t => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) ?_).symm
    intro t
    have h1 := posPl_true_one (notSg hg) t
    have h2 := FOrb_step D j (D.what₂.places.resChar w) (true, t) 1
    have h3 := errF_posPl (L := L) K ce j (D.what₂.places.resChar w) (true, t) 1
    rw [h1] at h2 h3
    simp only [h2, h3]

end GlobalTheory.TwU.SiteSys
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.LocOpAct

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cosetSum_mem_fixed (ρ : Representation ℂ G V) {K N : Subgroup G} [Fintype (K ⧸ N.subgroupOf K)] {v : V}
    (hv : v ∈ GroundTheory.Automorphic.fixedVectors ρ N) :
    GroundTheory.Automorphic.cosetSum ρ K N v ∈ GroundTheory.Automorphic.fixedVectors ρ K := by
  intro k hk

  rw [GroundTheory.Automorphic.cosetSum_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := GroundTheory.Automorphic.act_eq_of_mk_eq ρ hv (a := ⟨k, hk⟩ * Quotient.out q)
    (b := Quotient.out ((⟨k, hk⟩ : K) • q)) (by
      rw [QuotientGroup.out_eq']; conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl)
  simpa using this

theorem opOf_eq (ρ : Representation ℂ G V) (f : G →₀ ℂ) (v : V) :
    GlobalTheory.Cong.opOf ρ f v = (f.sum fun g c => c • ρ g) v := by
  simp [GlobalTheory.Cong.opOf, Finsupp.sum, LinearMap.sum_apply]

theorem opOf_map {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (τ : Representation ℂ G W) (F : V →ₗ[ℂ] W) (hF : ∀ g v, F (ρ g v) = τ g (F v)) (f : G →₀ ℂ) (v : V) :
    F (GlobalTheory.Cong.opOf ρ f v) = GlobalTheory.Cong.opOf τ f (F v) := by

  simp only [GlobalTheory.Cong.opOf, Finsupp.sum, map_sum, map_smul, hF]

end GlobalTheory.LocOpAct

theorem GlobalTheory.Cong.opOf_locU_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ (Kw : Subgroup (GL (Fin a) (w.adicCompletion E))), IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))) → IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ), (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) → ∃ f' : UA E a →₀ ℂ, (∀ g ∈ f'.support, g ∈ locU a w ∧ f' g = f (cLoc w g)) ∧ ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) f' φ = z σ • φ := by
  classical
  intro E _ _ _ a w hw Kw hKc hKo f z hf
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw
  let e : locU a w ≃* GL (Fin a) (w.adicCompletion E) :=
    MulEquiv.ofBijective ((cLoc w).comp (locU a w).subtype) hbij
  let j : GL (Fin a) (w.adicCompletion E) →* UA E a := (locU a w).subtype.comp e.symm.toMonoidHom
  let ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (UA E a → ℂ) := (RU E a).comp j
  have hcj : ∀ g, cLoc w (j g) = g := fun g => e.apply_symm_apply g
  have hinj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  haveI : CompactSpace Kw := isCompact_iff_compactSpace.1 hKc
  have hfin : ∀ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) →
      Finite (Kw ⧸ N.subgroupOf Kw) := fun N hN =>
    Subgroup.quotient_finite_of_isOpen _ (by rw [Subgroup.coe_subgroupOf]; exact hN.preimage continuous_subtype_val)
  refine ⟨f.mapDomain j, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact ⟨(e.symm h).2, by rw [Finsupp.mapDomain_apply_of_injective hinj, hcj]⟩
  · intro U hU σ hσ φ hφU hφK
    have hop : ∀ ψ, opOf (RU E a) (f.mapDomain j) ψ = opOf ρ' f ψ := by
      intro ψ
      simp only [GlobalTheory.Cong.opOf]
      rw [Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b c₁ c₂; simp [add_smul])]
      rfl
    rw [hop]
    have hFint : ∀ (F : {F : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, F v ∈ U) ∧
        ∀ (x : locU a w) v, F (σ.ρ (cLoc w x) v) = RU E a x (F v)}) g v, F.1 (σ.ρ g v) = ρ' g (F.1 v) := by
      intro F g v
      have h := F.2.2 (e.symm g) v
      have h2 : cLoc w ((e.symm g : locU a w) : UA E a) = g := hcj g
      rw [h2] at h
      exact h
    let T : Module.End ℂ (UA E a → ℂ) := (f.sum fun g c => c • ρ' g) - z σ • 1
    have hT : ∀ ψ, T ψ = opOf ρ' f ψ - z σ • ψ := fun ψ => by
      rw [GlobalTheory.LocOpAct.opOf_eq]; rfl
    have key := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hσ φ hφU
    have hC : ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' φ) = 0 := by
      refine Submodule.iSup_induction _ (motive := fun ψ => ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)),
        IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' ψ) = 0) key ?_ ?_ ?_
      · rintro F _ ⟨v, rfl⟩
        refine ⟨GroundTheory.Automorphic.stabilizerOf σ.ρ v, σ.smooth v, fun N' hN' hle => ?_⟩
        haveI := hfin N' hN'
        haveI := Fintype.ofFinite (Kw ⧸ N'.subgroupOf Kw)
        have hv : v ∈ GroundTheory.Automorphic.fixedVectors σ.ρ N' := fun n hn => hle hn
        have hu := GlobalTheory.LocOpAct.cosetSum_mem_fixed σ.ρ (K := Kw) hv
        have hcs : GroundTheory.Automorphic.cosetSum ρ' Kw N' (F.1 v) = F.1 (GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v) := by

          rw [GroundTheory.Automorphic.cosetSum_apply, GroundTheory.Automorphic.cosetSum_apply, map_sum]
          simp only [hFint]
        have hfix : GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v ∈ GlobalTheory.PRep.fixed σ.ρ Kw := fun k => by
          show σ.ρ k _ = ((1 : Kw →* ℂˣ) k : ℂ) • _
          simp [hu k k.2]
        rw [hcs, hT, ← GlobalTheory.LocOpAct.opOf_map σ.ρ ρ' F.1 (hFint F) f, hf σ _ hfix, map_smul, sub_self]
      · exact ⟨⊤, by simp, fun N' _ _ => by simp⟩
      · rintro x y ⟨N₁, h₁, hx⟩ ⟨N₂, h₂, hy⟩
        refine ⟨N₁ ⊓ N₂, by rw [Subgroup.coe_inf]; exact h₁.inter h₂, fun N' hN' hle => ?_⟩
        rw [map_add (f := _), map_add (f := _), hx N' hN' (hle.trans inf_le_left), hy N' hN' (hle.trans inf_le_right), add_zero]
    obtain ⟨N, hN, hNφ⟩ := hC
    haveI := hfin N hN
    haveI := Fintype.ofFinite (Kw ⧸ N.subgroupOf Kw)
    have hφ : φ ∈ GroundTheory.Automorphic.fixedVectors ρ' Kw := fun k hk => by
      have := hφK (j k) (e.symm k).2 (by rw [hcj]; exact hk)
      exact this
    have h0 := hNφ N hN le_rfl
    rw [GroundTheory.Automorphic.cosetSum_of_mem ρ' hφ, map_smul] at h0
    have hne : (Fintype.card (Kw ⧸ N.subgroupOf Kw) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [smul_eq_zero] at h0
    have h1 := h0.resolve_left hne
    rw [hT, sub_eq_zero] at h1
    exact h1
end
end
