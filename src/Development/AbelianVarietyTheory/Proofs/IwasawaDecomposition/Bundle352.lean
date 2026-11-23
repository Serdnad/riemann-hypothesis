module

public import Formalism.LocalToGlobal.Columns.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle739
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle039
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle294
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem PtY.mv_dn_facts {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n)
    (p : PtY ST SG Q y) (P : ST) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) (v : HeightOneSpectrum (𝓞 X.F))
    (hov : IsOver v P.1) (hne : conjPrime₂ P.1 ≠ P.1) (hconj : IsOver v (conjPrime₂ P.1)) :
    (p.mv (p.1.1.deco.dn P f')).1.2 = p.1.2 ∧ (p.mv (p.1.1.deco.dn P f')).1.1.fr = p.1.1.fr ∧
      Deco.SameOff ST SG v p.1.1.deco.1 (p.mv (p.1.1.deco.dn P f')).1.1.deco.1 := by
  classical

  have key : Deco.SameOff ST SG v p.1.1.deco.1 (p.1.1.deco.dn P f').1 := by
    unfold DecoSet.dn
    split_ifs with hok
    · refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun _ _ => rfl⟩
      · have hQP : Q ≠ P.1 := fun h => hQ (by rw [h]; exact hov)
        have hQc : Q ≠ conjPrime₂ P.1 := fun h => hQ (by rw [h]; exact hconj)
        exact ((p.1.1.deco.2.dnN_spec P hne).2.2.1 Q hQP hQc).localization_eq.symm
      · have hQP : Q ≠ P := fun h => hQ (by rw [h]; exact hov)
        show p.1.1.deco.1.f Q = Function.update p.1.1.deco.1.f P f' Q
        rw [Function.update_of_ne hQP]
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

  suffices H : ∀ d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG), Deco.SameOff ST SG v p.1.1.deco.1 d.1 →
      (p.mv d).1.2 = p.1.2 ∧ (p.mv d).1.1.fr = p.1.1.fr ∧
        Deco.SameOff ST SG v p.1.1.deco.1 (p.mv d).1.1.deco.1 from H _ key
  intro d hd
  by_cases h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · have e : (p.mv d).1 = ((⟨(d, p.1.1.1.2), h.1⟩ : DecoF X.E n ST SG Q), p.1.2) :=
      congrArg Subtype.val (dif_pos h)
    rw [e]
    exact ⟨rfl, rfl, hd⟩
  · have e : p.mv d = p := dif_neg h
    rw [e]
    exact ⟨rfl, rfl, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

end GlobalTheory.Mem.Col2
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IsoTypScalar

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem heckeD_eq_sum_of {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {J : Subgroup (GAf L n)}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have tr : ∀ x ∈ D, ∀ y ∈ D, TrivOutside {v} (x⁻¹ * y) := fun x hx y hy =>
    GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy)
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dite_eq_left hc]
    have ht := tr γ (h1 γ hγ) _ hc.choose_spec.1
    have hu : γ⁻¹ * hc.choose ∈ Umax L n := (hJ _ ht).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu ht) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hJ _ (tr γ (h1 γ hγ) δ (h1 δ hδ))).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hJ _ (tr γ (h1 γ hγ) x hx)).2 e)⟩)
    · exact absurd (dite_eq_right h) hc

theorem isoTyp_scalar (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L))))
    (hyp : NG.HypOutside J χ B) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ) (hsB : s.v ∉ B) (hϖ : IsUnif L s.v ϖ) :
    ∃ c : ℂ, ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → NG.tN J s ϖ k f = c • f := by
  classical
  have tc : ∀ κ : GAf L n, TrivOutside {s.v} κ → TrivOutside Bᶜ κ := fun κ hκ v hv =>
    hκ v fun h => hv (by rw [Set.mem_compl_iff, Set.mem_singleton_iff.1 h]; exact hsB)
  have hJU : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n) := fun κ hκ => (hyp κ (tc κ hκ)).1
  have hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite :=
    GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level L n (Umax L n) 1 ∅ (fun κ _ => ⟨Iff.rfl, fun _ => MonoidHom.one_apply _⟩) s ϖ k
      (Set.notMem_empty _) hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax L n) _ hfin
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun _ hx => hx.1
  set q : ℂ := ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ with hq
  have hJeq : ∀ f : GAf L n → a.W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      NG.tN J s ϖ k f = q • ∑ γ ∈ R, NG.rt L n γ f := fun f hf => by
    rw [NG.tN, heckeD_eq_sum_of hJU hD hR1 hR2 hf]
  have hUeq : ∀ f : GAf L n → a.W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      NG.tN (Umax L n) s ϖ k f = q • ∑ γ ∈ R, NG.rt L n γ f := fun f hf => by
    rw [NG.tN, GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := s.v) hD hR1 hR2 hf]
  obtain ⟨c, hc⟩ := GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical L n a S hS s ϖ k hϖ
  have hS0 : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      q • ∑ γ ∈ R, NG.rt L n γ f = c • f := fun f hf hx => (hUeq f hx).symm.trans (hc f hf hx)

  have hiso : ∀ S' : Submodule ℂ (GAf L n → a.W), NG.IsoRep S S' → ∀ f ∈ S',
      (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → q • ∑ γ ∈ R, NG.rt L n γ f = c • f := by
    rintro S' ⟨T, hT⟩ f hf hfx
    set g : S := T.symm ⟨f, hf⟩ with hg
    have hTg : ((T g : S') : GAf L n → a.W) = f := by simp [g]
    have hgx : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (g : GAf L n → a.W) = g := by
      intro κ h1 h2
      have e := hT κ g ⟨NG.rt L n κ (g : GAf L n → a.W), hS.1.stable κ _ g.2⟩ rfl
      rw [hTg, hfx κ h1 h2] at e
      have e2 : T ⟨NG.rt L n κ (g : GAf L n → a.W), hS.1.stable κ _ g.2⟩ = T g := Subtype.ext (e.trans hTg.symm)
      exact congrArg Subtype.val (T.injective e2)
    have key : (c • g : S) = q • ∑ γ ∈ R, (⟨NG.rt L n γ (g : GAf L n → a.W), hS.1.stable γ _ g.2⟩ : S) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_sum]
      exact (hS0 g g.2 hgx).symm
    have hterm : ∀ γ : GAf L n,
        ((T ⟨NG.rt L n γ (g : GAf L n → a.W), hS.1.stable γ _ g.2⟩ : S') : GAf L n → a.W) = NG.rt L n γ f := by
      intro γ
      rw [hT γ g _ rfl, hTg]
    have := congrArg (fun u : S => ((T u : S') : GAf L n → a.W)) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Submodule.coe_smul, Submodule.coe_sum, hTg, hterm] at this
    exact this.symm

  have hsum : ∀ t : Finset (Submodule ℂ (GAf L n → a.W)),
      (↑t : Set (Submodule ℂ (GAf L n → a.W))) ⊆ {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'} →
      (∀ h, ∀ f ∈ ⨆ S' ∈ t, S', NG.rt L n h f ∈ ⨆ S' ∈ t, S') ∧
      ∀ f ∈ ⨆ S' ∈ t, S', (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
        q • ∑ γ ∈ R, NG.rt L n γ f = c • f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot]
      refine ⟨fun h f hf => ?_, fun f hf _ => ?_⟩
      · rw [hf, map_zero]
      · simp [hf]
    | insert S₁ t hS₁ ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨hst, hfx⟩ := ih hs.2
      have h1 := hs.1
      rw [Finset.iSup_insert]
      refine ⟨fun h f hf => ?_, fun f hf hfix => ?_⟩
      · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (h1.1.1.stable h x hx) (hst h y hy)
      · by_cases hd : S₁ ⊓ (⨆ S' ∈ t, S') = ⊥
        · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
          have hxy : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ x = x ∧ NG.rt L n κ y = y := by
            intro κ hκ hκ'
            have e := hfix κ hκ hκ'
            rw [map_add (f := _)] at e
            have e1 : NG.rt L n κ x - x = y - NG.rt L n κ y := by
              rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
            have hm : NG.rt L n κ x - x ∈ S₁ ⊓ (⨆ S' ∈ t, S') :=
              ⟨S₁.sub_mem (h1.1.1.stable κ x hx) hx, e1 ▸ Submodule.sub_mem _ hy (hst κ y hy)⟩
            rw [hd, Submodule.mem_bot] at hm
            refine ⟨sub_eq_zero.1 hm, ?_⟩
            rw [hm] at e1
            exact (sub_eq_zero.1 e1.symm).symm
          simp only [map_add (f := _), Finset.sum_add_distrib, smul_add]
          rw [hiso S₁ h1.2 x hx fun κ h h' => (hxy κ h h').1, hfx y hy fun κ h h' => (hxy κ h h').2]
        · have hsub : NG.IsSubrep a.ρ (S₁ ⊓ (⨆ S' ∈ t, S')) :=
            ⟨inf_le_left.trans h1.1.1.le, fun h f hf => ⟨h1.1.1.stable h f hf.1, hst h f hf.2⟩⟩
          have heq : S₁ ⊓ (⨆ S' ∈ t, S') = S₁ := (h1.1.2.2 _ hsub inf_le_left).resolve_left hd
          have hle : S₁ ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
          exact hfx f ((sup_le hle le_rfl) hf) hfix
  refine ⟨c, fun f hf hT => ?_⟩
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f := by
    intro κ h1 h2
    have hκ : κ ∈ J := (hJU κ h2).2 h1
    have e := hT.2 ⟨κ, hκ⟩
    rw [(hyp κ (tc κ h2)).2 hκ] at e
    simpa using e
  rw [hJeq f hfix]
  unfold NG.isoTyp at hf
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact (hsum t ht).2 f hft hfix

theorem main : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := by
  intro D μ j Mr B _ hyp S hS s ϖ k hsB hϖ _ _
  obtain ⟨c, hc⟩ := isoTyp_scalar Mr.wt Mr.J Mr.χ B hyp S hS s ϖ k hsB hϖ
  refine ⟨c, fun y hy => hc _ (Submodule.mem_comap.1 hy) ?_⟩
  rw [← Mr.real_range]
  exact ⟨y, rfl⟩

end GlobalTheory.IsoTypScalar

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubst

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex GlobalTheory.Ker.FockAlg

section Generic

variable {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {κ : Type} [Fintype κ] (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (hA' : ∀ i f, P f → P (A' i f)) (hc' : ∀ i j f, P f → A' i (A' j f) = A' j (A' i f))
    (Aadd' : ∀ i f f', P f → P f' → A' i (f + f') = A' i f + A' i f')
    (Asm' : ∀ i (a : ℂ) f, P f → A' i (a • f) = a • A' i f)
    (c : ι → κ → ℂ) (r : ι → κ → ι) (h : ∀ i f, P f → A' i f = ∑ b, c i b • A (r i b) f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' f Q = pureTensorL A f
      (MvPolynomial.aeval (fun v : ι => ∑ b, c v b • (MvPolynomial.X (r v b) : MvPolynomial ι ℂ)) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), MvPolynomial.C_mul',
      map_smul, map_smul, pure_one, pure_one]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>

    rw [mul_comm, pure_X_mul hadd hsm hA' hc' Aadd' Asm' hf, hp, h _ _ (pure_mem hadd hsm hA hf _), map_mul,
    MvPolynomial.aeval_X, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc, map_smul, pure_X_mul hadd hsm hA hc Aadd Asm hf]

end Generic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) (t : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)

include hψ hθ hf

theorem dRho_csmul (w : ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (w • u) f =
      (w.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ u f + (w.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (I • u) f := by
  have e : w • u = (w.re : ℂ) • u + (w.im : ℂ) • (I • u) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (dRho_laws hψ hθ hf τ _).2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_dir_add (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (z + z') f =
      aPlus (heisO ψ S T) θ τ (cplxO s t) z f + aPlus (heisO ψ S T) θ τ (cplxO s t) z' f := by
  simp only [aPlus_eq, GlobalTheory.OrientedRealForm.cplxO_add, fun z => (dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem aPlus_dir_zero : aPlus (heisO ψ S T) θ τ (cplxO s t) 0 f = 0 := by
  have := aPlus_dir_add hψ hθ τ s t hf 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem aPlus_dir_sum {κ : Type} (F : Finset κ) (z : κ → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (∑ b ∈ F, z b) f = ∑ b ∈ F, aPlus (heisO ψ S T) θ τ (cplxO s t) (z b) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using aPlus_dir_zero hψ hθ τ s t hf
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aPlus_dir_add hψ hθ τ s t hf, ih]

theorem aPlus_dir_smul (e : Bool) (w : ℂ) {u : Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hu : cplxO s t u = ((if e then 1 else -1 : ℂ) * I) • u) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (w • u) f =
      (if e then w else starRingEnd ℂ w) • aPlus (heisO ψ S T) θ τ (cplxO s t) u f := by
  have h1 : cplxO s t (w • u) = (w * ((if e then 1 else -1 : ℂ) * I)) • u := by
    rw [← smul_smul, ← hu]
    unfold cplxO
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  rw [aPlus_eq, aPlus_eq, h1, hu, dRho_csmul hψ hθ τ hf w, dRho_csmul hψ hθ τ hf (w * _),
    dRho_csmul hψ hθ τ hf (_ * I)]
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, w = x + y * I := ⟨w.re, w.im, (Complex.re_add_im w).symm⟩
  cases e
  · simp only [Bool.false_eq_true, if_false, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;> simp <;> ring_nf <;> simp
  · simp only [if_true]
    match_scalars <;> simp <;> ring_nf <;> simp

omit hψ hθ hf

theorem unitMap_mul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (j : Fin n) : unitMap B (B' * k) a j = ∑ b, k b a • unitMap B B' b j := by
  have e : k * single a j (1 : ℂ) = ∑ b, k b a • single b j (1 : ℂ) := by
    ext p q
    by_cases h : j = q
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, h]
  unfold unitMap
  rw [Matrix.mul_assoc B', e, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxO_unitMap {S' : D.what₂.Tau → SPar} (M : DSModel T S') {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin T.rank) (j : Fin n) : cplxO 1 (cart M τ) (unitMap B (onb M τ) b j) =
      ((if M.ε τ b then 1 else -1 : ℂ) * I) • unitMap B (onb M τ) b j := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have e : Formalism.REAL.Jm (M.ε τ) * single b j (1 : ℂ) = (if M.ε τ b then 1 else -1 : ℂ) • single b j (1 : ℂ) := by
    ext p q
    rw [Formalism.REAL.Jm, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : b = p
    · rw [h]
    · simp [h]
  unfold cplxO unitMap cart onb
  rw [Matrix.mul_one, mul_comm _ I, ← smul_smul]
  congr 1
  calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * single b j (1 : ℂ)) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, e, Matrix.mul_smul, Matrix.smul_mul]

theorem kset_zero {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n}
    (h : ε b ≠ ε a) : k b a = 0 := by
  have e := congrFun (congrFun hk.2 b) a
  rw [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at h e <;> simp at e <;>
    first | linear_combination (1 / 2 : ℂ) * e | linear_combination (-1 / 2 : ℂ) * e

theorem pureTensorO_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  intro D ψ θ S T S' M BS f k c hψ hθ hS hf hk hc P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hA : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f f', IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T f' → aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (f + f') =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f +
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f' :=
    fun _ _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f :=
    fun _ _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i j f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j f) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ i j _ h => aPlus_comm (sS := fun _ => 1) (sT := cart M) hψ hθ i.1 _ hS hT j.1 _ h
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (fun τ => onb M τ * k τ) i g =
      ∑ b, c i.1 b i.2.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (i.1, b, i.2.2) g := by
    rintro ⟨τ, a, j⟩ g hg
    simp only [aPlusAll]
    rw [unitMap_mul, aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aPlus_dir_smul hψ hθ τ _ _ hg _ _ (cplxO_unitMap τ M _ b j), hc]
    by_cases h : M.ε τ b = M.ε τ a
    · rw [h]
    · rw [kset_zero (hk τ) h]
      simp
  unfold pureTensorO
  exact pure_subst (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (hA _) (Ac _) (Aadd _) (Asm _) (hA _) (Ac _) (Aadd _) (Asm _)
    (fun v b => c v.1 b v.2.1) (fun v b => (v.1, b, v.2.2)) key hf P

end GlobalTheory.FockSubst
end
