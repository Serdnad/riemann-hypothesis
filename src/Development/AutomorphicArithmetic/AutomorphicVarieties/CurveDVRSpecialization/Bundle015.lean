module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_lambda_characters :
    UpperTheory.V.Pr.CrLam := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k v A hA hM
  haveI := Φ.cv v
  haveI := Φ.t2v v
  obtain ⟨hemb, -, -⟩ := galEmbTop ℚ L Ω
  let e1 : Dec (F := L) A →* G ℚ Ω := (galEmb ℚ L Ω).comp (Dec (F := L) A).subtype
  let e2 : Φ.Gv v →* G ℚ Ω := (upl Ω L).subtype.comp (k.j v)
  have he1 : Function.Injective e1 := hemb.injective.comp Subtype.val_injective
  have he2 : Function.Injective e2 := Subtype.val_injective.comp (k.j_inj v)
  have hrange : e1.range = e2.range := by
    ext τ
    constructor
    · rintro ⟨g, rfl⟩
      have hup : e1 g ∈ upl Ω L := by
        have := galEmb_mem ℚ L Ω (g : G L Ω)
        rw [k.gal] at this
        exact this.1
      have hdec : e1 g ∈ Dec (F := ℚ) (k.pl v) := by
        show galEmb ℚ L Ω g ∈ _
        rw [← hA, galEmb_mem_Dec]
        exact g.2
      obtain ⟨x, hx⟩ := (k.j_range v ⟨_, hup⟩).2 hdec
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      have hdec : e2 x ∈ Dec (F := ℚ) A := by
        rw [hA]
        exact (k.j_range v (k.j v x)).1 ⟨x, rfl⟩
      have hup : e2 x ∈ upl Ω L := (k.j v x).2
      have hker : e2 x ∈ η.ker := k.split A hM ⟨hdec, hup⟩
      have hfix : e2 x ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨hup, hker⟩
      let g : G L Ω := AlgEquiv.ofRingEquiv (f := (e2 x).toRingEquiv) (fun y => hfix y)
      have hg : galEmb ℚ L Ω g = e2 x := by
        ext y
        rfl
      have hgd : g ∈ Dec (F := L) A := by
        rw [← galEmb_mem_Dec (k := ℚ), hg]
        exact hdec
      exact ⟨⟨g, hgd⟩, hg⟩
  let m : Dec (F := L) A ≃* Φ.Gv v :=
    (MonoidHom.ofInjective he1).trans ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective he2).symm)
  have hm : ∀ g, e2 (m g) = e1 g := by
    intro g
    have := MonoidHom.ofInjective_apply he2 (x := m g)
    rw [← this, ← MonoidHom.ofInjective_apply he1 (x := g)]
    simp [m]
  have hinv : Continuous m.symm := by
    have hcomp : e1 ∘ m.symm = e2 := by
      funext x
      rw [Function.comp_apply, ← hm, MulEquiv.apply_symm_apply]
    have he1emb : Topology.IsEmbedding e1 := hemb.comp Topology.IsEmbedding.subtypeVal
    rw [he1emb.continuous_iff, hcomp]
    exact continuous_subtype_val.comp (k.j_cont v)
  have hfwd : Continuous m := by
    have := hinv.continuous_symm_of_equiv_compact_to_t2 (f := m.symm.toEquiv)
    simpa using this
  refine ⟨{ m with continuous_toFun := hfwd, continuous_invFun := hinv }, fun g => ?_⟩
  exact hm g
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : W.Plc k} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  have hlift : IsLift (RingEquiv.refl k) σ.toRingEquiv := fun x => σ.commutes x
  have hmem : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A := by
    intro x
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨σ, fun τ hτ => ?_⟩
  have h1 := conjGal_mem_Ine hlift hmem hτ
  have heq : conjGal hlift τ = σ⁻¹ * τ * σ := AlgEquiv.ext fun x => rfl
  rw [← heq]
  exact h1

private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (W.Plc k)} {A : ValuationSubring Ω} {v : W.Plc k} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem normal_map {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (N : Subgroup F.G₀) (hN : N.Normal)
    (hc : ∀ g ∈ N, F.conj g ∈ N) : (N.map F.η.ker.subtype).Normal := by
  constructor
  rintro _ ⟨m, hm, rfl⟩ γ
  by_cases hγ : F.η γ = 1
  · exact ⟨⟨γ, hγ⟩ * m * (⟨γ, hγ⟩ : F.G₀)⁻¹, hN.conj_mem m hm _, rfl⟩
  · have hγ' : F.η γ = -1 := (Int.units_eq_one_or _).resolve_left hγ
    have h0 : F.η (F.c⁻¹ * γ) = 1 := by
      rw [map_mul, map_inv, F.η_c, hγ']
      simp
    let γ0 : F.G₀ := ⟨F.c⁻¹ * γ, h0⟩
    refine ⟨F.conj (γ0 * m * γ0⁻¹), hc _ (hN.conj_mem m hm γ0), ?_⟩
    show F.c * (F.c⁻¹ * γ * (m : F.Γ) * (F.c⁻¹ * γ)⁻¹) * F.c⁻¹ = γ * (m : F.Γ) * γ⁻¹
    group

theorem UpperTheory.frame_criterion_kernel :
    UpperTheory.V.Pr.CrKer := by
  unfold UpperTheory.V.Pr.CrKer
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS π hπ N hN hNc hNconj hIu hI0
  let N' : Subgroup V.frame.Γ := N.map V.frame.η.ker.subtype
  haveI hN'n : N'.Normal := normal_map V.frame N hN hNconj
  have hG0c : IsClosed (V.frame.η.ker : Set V.frame.Γ) :=
    Subgroup.isClosed_of_isOpen _ V.frame.η_open
  have hN'c : IsClosed (N' : Set V.frame.Γ) := by
    rw [Subgroup.coe_map]
    exact hG0c.isClosedEmbedding_subtypeVal.isClosedMap _ hNc
  let K : Subgroup (G (W.Lp L) Ω) := N'.comap (toGS Ω V.S')
  have hKc : IsClosed (K : Set (G (W.Lp L) Ω)) := hN'c.preimage (continuous_toGS Ω V.S')
  haveI hKn : K.Normal := hN'n.comap _
  let Kup : Subgroup (upl Ω L) := K.map (toUpl Ω L)
  haveI hKupn : Kup.Normal := hKn.map _ toUpl_surj
  have hind : Topology.IsInducing (toUpl Ω L) :=
    (Topology.IsInducing.subtypeVal.of_comp_iff).1 (galEmbTop ℚ (W.Lp L) Ω).1.isInducing
  have hKupc : IsClosed (Kup : Set (upl Ω L)) := by
    obtain ⟨t, ht, hpre⟩ := hind.isClosed_iff.1 hKc
    rw [Subgroup.coe_map, ← hpre, Set.image_preimage_eq t toUpl_surj]
    exact ht
  have hgen : ∀ u : upl Ω L, ∀ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 →
      (u : G ℚ Ω) ∈ Ine B' → barChar O Ψ (u : G ℚ Ω) = 1 → u ∈ Kup := by
    intro u B' hl hIne hbar
    obtain ⟨τ, hτ⟩ := toUpl_surj (Ω := Ω) (L := L) u
    refine ⟨τ, ?_, hτ⟩
    have hτI : τ ∈ Ine (F := W.Lp L) B' := by
      rw [← hτ] at hIne
      exact hIne
    by_cases htop : B' = ⊤
    · have hbot := ((places (W.Lp L) Ω l B').2.1 htop).1
      rw [hbot] at hτI
      rw [Subgroup.mem_bot.1 hτI]
      exact K.one_mem
    obtain ⟨v, hv⟩ := (places (W.Lp L) Ω l B').1 htop
    by_cases hvS : v ∈ V.S'
    · have hvS' : v ∈ s.S := hS ▸ hvS
      obtain ⟨h, hh⟩ := conj_ine (s.hA v) hv
      have hτ' := hh τ hτI
      obtain ⟨t, ht⟩ := s.unr (s.A v) v (s.hA v) hτ'
      have htI : t ∈ Ine (F := L) (s.A v) := by
        have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) (s.A v) := by
          rw [ht]
          exact hτ'
        exact h1
      have hprN : V.pr t ∈ N := by
        rcases hvS' with hlv | hvSt | hv0
        · exfalso
          exact hl ((natCast_place hv l).2 hlv)
        · apply hIu ⟨v, hvSt⟩ (V.pr t) ⟨t, htI, rfl⟩
          rw [hπ t, k.galois_link_projection_coe, k.psi]
          change barChar O Ψ (galEmb ℚ (W.Lp L) Ω (W.resP L Ω t)) = 1
          rw [ht, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
            mul_comm ((barChar O Ψ) ((galEmb ℚ (W.Lp L) Ω) h))⁻¹ _, inv_mul_cancel_right]
          have hu : (galEmb ℚ (W.Lp L) Ω) τ = (u : G ℚ Ω) := by
            rw [← hτ]
            rfl
          rw [hu]
          exact hbar
        · apply hI0
          subst hv0
          exact ⟨t, htI, rfl⟩
      have hτ'N : toGS Ω V.S' (h⁻¹ * τ * h) ∈ N' := by
        refine ⟨V.pr t, hprN, ?_⟩
        change toGS Ω V.S' (W.resP L Ω t) = _
        rw [ht]
      have hconj := hN'n.conj_mem _ hτ'N (toGS Ω V.S' h)
      have heq : toGS Ω V.S' h * toGS Ω V.S' (h⁻¹ * τ * h) * (toGS Ω V.S' h)⁻¹ = toGS Ω V.S' τ := by
        simp only [map_mul, map_inv]
        group
      change toGS Ω V.S' τ ∈ N'
      rw [← heq]
      exact hconj
    · change toGS Ω V.S' τ ∈ N'
      rw [ine_NS hvS hv hτI]
      exact N'.one_mem
  have hpker : k.p.ker ≤ Kup := by
    rw [k.p_ker]
    apply Subgroup.topologicalClosure_minimal _ _ hKupc
    apply Subgroup.normalClosure_le_normal
    rintro u ⟨B', hl, hIne, -, hbar⟩
    exact hgen u B' hl hIne hbar
  intro g0 hg0
  obtain ⟨g, rfl⟩ := pr_surj V g0
  have hp0 : k.p0 g = 1 := by
    rw [← hπ g]
    exact hg0
  have hpk : toUpl Ω L (W.resP L Ω g) ∈ k.p.ker := by
    rw [MonoidHom.mem_ker, ← k.galois_link_projection_coe, hp0]
    rfl
  obtain ⟨τ, hτK, hτeq⟩ := hpker hpk
  have hτg : τ = W.resP L Ω g := toUpl_inj hτeq
  obtain ⟨m, hm, hmeq⟩ := hτK
  have hpr : V.pr g = m := by
    apply Subtype.ext
    change toGS Ω V.S' (W.resP L Ω g) = (m : V.frame.Γ)
    rw [← hτg]
    exact hmeq.symm
  rw [hpr]
  exact hm
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

private theorem ker_pr_le {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (M : ℕ)
    (hM : ∀ v : W.Plc (W.Lp L), ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → v ∈ V.S') (K : Subgroup (G L Ω))
    (hK : IsClosed (K : Set (G L Ω)))
    (hI : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := L) A ≤ K) : V.pr.ker ≤ K := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hg' : toGS Ω V.S' (W.resP L Ω g) = 1 := congrArg Subtype.val hg
  have hNS : W.resP L Ω g ∈ NS Ω V.S' := by
    unfold toGS at hg'
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg'
  let Kp : Subgroup (G (W.Lp L) Ω) := K.map (W.resP L Ω)
  have hKp : IsClosed (Kp : Set (G (W.Lp L) Ω)) := by
    rw [Subgroup.coe_map]
    exact ((hK.isCompact).image W.continuous_resP).isClosed
  have hX : ∀ v : W.Plc (W.Lp L), v ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∀ τ ∈ Ine (F := W.Lp L) A, τ ∈ Kp := by
    intro v hv A hA τ hτ
    obtain ⟨t, ht⟩ := s.unr A v hA hτ
    have hM' : ¬ A.valuation (M : Ω) < 1 := by
      rw [natCast_place hA]
      exact fun h => hv (hM v h)
    have htI : t ∈ Ine (F := L) A := by
      have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) A := by
        rw [ht]
        exact hτ
      exact h1
    exact ⟨t, hI A hM' htI, ht⟩
  have hNSle : NS Ω V.S' ≤ Kp := by
    letI : MulAction (G (W.Lp L) Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
    unfold NS
    apply Subgroup.topologicalClosure_minimal _ _ hKp
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨x, hx, hconj⟩ := hy
    simp only [Set.mem_iUnion] at hx
    obtain ⟨v, hv, A, hA, hxA⟩ := hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    subst hc
    have hlift : IsLift (RingEquiv.refl (W.Lp L)) (c⁻¹).toRingEquiv := fun z => (c⁻¹).commutes z
    have hmem : ∀ z : Ω, (c⁻¹).toRingEquiv z ∈ A ↔ z ∈ c • A := by
      intro z
      exact (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := c) (S := A) (x := z)).symm
    have h1 := conjGal_mem_Ine hlift hmem hxA
    have heq : conjGal hlift x = c * x * c⁻¹ := AlgEquiv.ext fun z => rfl
    have hcA : ∀ z : Ω, c.toRingEquiv z ∈ c • A ↔ z ∈ A := by
      intro z
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := c) (S := A) (x := z)
    have hplace : IsPlaceOver (c • A) v := by
      intro z
      have hz : c.toRingEquiv ((algebraMap (W.Lp L) Ω) (z : W.Lp L)) = (algebraMap (W.Lp L) Ω) (z : W.Lp L) :=
        c.commutes _
      rw [← hz, val_lt_one hcA]
      exact hA z
    rw [← heq]
    exact hX v hv (c • A) hplace _ h1
  obtain ⟨g', hg'K, hg'eq⟩ := hNSle hNS
  have hgg : g' = g := by
    ext z
    exact DFunLike.congr_fun hg'eq z
  rw [← hgg]
  exact hg'K

private theorem coef_algebraMap_padicInt_eq (l : ℕ) [Fact l.Prime] (c₁ : Coef l) (z : ℤ_[l]) :
    ((algebraMap c₁.O c₁.O (algebraMap ℤ_[l] c₁.O z) : c₁.O) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := by
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  change algebraMap ℤ_[l] (PadicAlgCl l) z = _
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rfl

theorem UpperTheory.frame_criterion_level_kernel :
    UpperTheory.V.Pr.CrKap := by
  unfold UpperTheory.V.Pr.CrKap
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS c₁ ι n ka hka hO
  have hcont : Continuous ka := hka.alg.1
  let f : G L Ω →* c₁.O :=
    { toFun := fun g => ⟨(ka g : Qbar l), hO g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  let ka0 : G L Ω →* (c₁.O)ˣ := f.toHomUnits
  have hMS : ∀ v : W.Plc (W.Lp L), ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → v ∈ V.S' := by
    intro v hv
    rw [hS]
    by_cases hl : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact Or.inl hl
    · exact Or.inr (Or.inl ((x.St v).2 ⟨hv, hl⟩))
  have hKc : IsClosed (ka.ker : Set (G L Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hcont
  have hker : V.pr.ker ≤ ka.ker :=
    ker_pr_le V M hMS ka.ker hKc (fun A hA t ht => (MonoidHom.mem_ker).2 (hka.unr A hA t ht))
  have hker0 : V.pr.ker ≤ ka0.ker := by
    intro g hg
    have h1 : ka g = 1 := hker hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply Subtype.ext
    change (ka g : Qbar l) = ((1 : (Qbar l)ˣ) : Qbar l)
    rw [h1]
  have hsurj := pr_surj V
  let κ : V.frame.G₀ →* (c₁.O)ˣ :=
    V.pr.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨ka0, hker0⟩
  have hκ : ∀ g, κ (V.pr g) = ka0 g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  let φ : (c₁.O)ˣ →* (Qbar l)ˣ := Units.map (c₁.O.val : c₁.O →* Qbar l)
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hab
  have hφka : ∀ g, φ (ka0 g) = ka g := fun g => Units.ext rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro g
    rw [hκ g]
    rfl
  · rw [(X.So.adicCont l c₁).2]
    haveI : IsClosed (NS Ω V.S' : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'
    have hprc : Continuous V.pr := V.pr_cont W.continuous_resP
    have hq : Topology.IsQuotientMap V.pr := IsClosedMap.isQuotientMap hprc.isClosedMap hprc hsurj
    have hfun : (fun g : ↥V.η.ker => ((κ g : (c₁.O)ˣ) : c₁.O)) ∘ V.pr =
        fun g => (⟨(ka g : Qbar l), hO g⟩ : c₁.O) := by
      funext g
      simp only [Function.comp_apply, hκ]
      rfl
    have hc2 : Continuous ((fun g : ↥V.η.ker => ((κ g : (c₁.O)ˣ) : c₁.O)) ∘ V.pr) := by
      rw [hfun]
      exact (Units.continuous_val.comp hcont).subtype_mk hO
    exact hq.continuous_iff.2 hc2
  · intro g0
    obtain ⟨g, rfl⟩ := hsurj g0
    have hr : V.η (toGS Ω V.S' (W.resP L Ω g)) = 1 := (V.hη _).2 ⟨g, rfl⟩
    have hτr : s.c * W.resP L Ω g * s.c⁻¹ ∈ (W.resP L Ω).range := by
      apply (V.hη _).1
      simp only [map_mul, map_inv, hr, mul_one, mul_inv_cancel]
    obtain ⟨g', hg'⟩ := hτr
    have hconjpr : V.frame.conj (V.pr g) = V.pr g' := by
      apply Subtype.ext
      change toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω g) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω g')
      rw [hg', map_mul, map_mul, map_inv]
    have hσ : galEmb ℚ L Ω g' = σ * galEmb ℚ L Ω g * σ⁻¹ := by
      rw [← galEmb_resP g', ← galEmb_resP g, hg', map_mul, map_mul, map_inv, x.c]
    have hk := hka.conj g g' hσ
    have he : φ (V.frame.eps c₁.O c₁.O (V.pr g)) = cycBar L Ω l g := by
      apply Units.ext
      have hε : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
      change ((algebraMap c₁.O c₁.O (algebraMap ℤ_[l] c₁.O ((V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]))) : c₁.O) : Qbar l) =
        algebraMap ℚ_[l] (Qbar l) (((cycZ L Ω l g : ℤ_[l])) : ℚ_[l])
      rw [hε, coef_algebraMap_padicInt_eq]
    rw [hconjpr, hκ, hκ]
    apply hφ
    rw [map_mul, map_zpow, hφka, hφka, he]
    exact hk
end
