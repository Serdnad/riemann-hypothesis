module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAInj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle016
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle012
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.RhoPf

open Formalism.L2.SG.TypedSets

section Abstract

variable {G : Type} [Group G]

theorem mem_map_conj (K : Subgroup G) (x a : G) :
    a ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * a * x ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem stab_eq_map (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom =
      (Γ ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
  ext a
  rw [Subgroup.mem_inf, mem_map_conj, mem_map_conj, Subgroup.mem_inf, mem_map_conj]
  have e1 : (γ * x * k)⁻¹ * a * (γ * x * k) = k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k := by group
  have e2 : x⁻¹ * (γ⁻¹ * a * γ) * x = k * (k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k) * k⁻¹ := by group
  constructor
  · rintro ⟨ha, hK⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) ha) hγ, ?_⟩
    rw [e1] at hK
    rw [e2]
    exact K.mul_mem (K.mul_mem hk hK) (K.inv_mem hk)
  · rintro ⟨ha, hK⟩
    refine ⟨?_, ?_⟩
    · have e3 : a = γ * (γ⁻¹ * a * γ) * γ⁻¹ := by group
      rw [e3]
      exact Γ.mul_mem (Γ.mul_mem hγ ha) (Γ.inv_mem hγ)
    · rw [e1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hK) hk

theorem card_conj_eq (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  rw [stab_eq_map Γ K x γ k hγ hk]
  exact Subgroup.card_map_of_injective (MulAut.conj γ).injective

theorem card_out_eq (Γ K : Subgroup G) (x : G) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out (DoubleCoset.mk Γ K x))).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨γ, hγ, k, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
  rw [h]
  exact card_conj_eq Γ K x γ k hγ hk

end Abstract

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem massCl_comap (e : G' ≃* G) (Γ K : Subgroup G) :
    massCl (Γ.comap e.toMonoidHom) (K.comap e.toMonoidHom) = massCl Γ K := by
  set Γ' := Γ.comap e.toMonoidHom with hΓ'
  set K' := K.comap e.toMonoidHom with hK'
  have hstab : ∀ y : G', Nat.card ↥(Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom) := by
    intro y
    have hm : (Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom).map e.toMonoidHom =
        Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom := by
      ext a
      rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, mem_map_conj, mem_map_conj]
      simp [hΓ', hK', Subgroup.mem_comap, map_mul, map_inv]
    rw [← hm, Subgroup.card_map_of_injective e.injective]
  unfold massCl
  refine finsum_eq_of_bijective (fun c => DoubleCoset.mk Γ K (e (Quotient.out c))) ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (@DoubleCoset.eq _ _ Γ K _ _).mp h
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    refine (@DoubleCoset.eq _ _ Γ' K' _ _).mpr
      ⟨e.symm γ, by simpa [hΓ'] using hγ, e.symm k, by simpa [hK'] using hk, ?_⟩
    apply e.injective
    simp [map_mul, h2]
  · intro c
    obtain ⟨γ, hγ, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul Γ' K' (e.symm (Quotient.out c))
    refine ⟨DoubleCoset.mk Γ' K' (e.symm (Quotient.out c)), ?_⟩
    show DoubleCoset.mk Γ K (e (Quotient.out (DoubleCoset.mk Γ' K' (e.symm (Quotient.out c))))) = c
    rw [hout]
    conv_rhs => rw [← Quotient.out_eq c]
    refine ((@DoubleCoset.eq _ _ Γ K _ _).mpr ⟨e γ, hγ, e k, hk, ?_⟩).symm
    simp [map_mul]
  · intro c
    rw [card_out_eq, hstab]

end Transport

section Count

variable {G α : Type} [Group G]

theorem massCl_eq_sum (Γ K : Subgroup G) (S : Finset α) (ℓ : G → α) (w : α → ℝ)
    (hS : ∀ x, ℓ x ∈ S)
    (hrel : ∀ x y, ℓ x = ℓ y ↔ ∃ γ ∈ Γ, ∃ k ∈ K, y = γ * x * k)
    (hsurj : ∀ s ∈ S, ∃ x, ℓ x = s)
    (hw : ∀ x, ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℕ) : ℝ)⁻¹ = w (ℓ x)) :
    massCl Γ K = ∑ s ∈ S, w s := by
  unfold massCl
  have hout : ∀ x, ∃ γ ∈ Γ, ∃ k ∈ K, Quotient.out (DoubleCoset.mk Γ K x) = γ * x * k := by
    intro x
    obtain ⟨γ, hγ, k, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
    exact ⟨γ, hγ, k, hk, h⟩
  rw [← Finset.sum_coe_sort S w, ← finsum_eq_sum_of_fintype]
  refine finsum_eq_of_bijective (fun c => (⟨ℓ (Quotient.out c), hS _⟩ : {s // s ∈ S}))
    ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    have h' : ℓ (Quotient.out c1) = ℓ (Quotient.out c2) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (hrel _ _).mp h'
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    exact (@DoubleCoset.eq _ _ Γ K _ _).mpr ⟨γ, hγ, k, hk, h2⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, rfl⟩ := hsurj s hs
    refine ⟨DoubleCoset.mk Γ K x, Subtype.ext ?_⟩
    obtain ⟨γ, hγ, k, hk, h⟩ := hout x
    exact ((hrel _ _).mpr ⟨γ, hγ, k, hk, h⟩).symm
  · intro c
    exact hw _

end Count

end Formalism.L2.SG.RhoPf
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG6

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem rg_bwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    Prod.map φ' φ '' H.iotaGraph g t₁ ⊆ H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
  rintro _ ⟨⟨y', y⟩, ⟨x₁', x₁, hx₁'L, hx₁L, hd₁, hpe⟩, rfl⟩
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  have hcO : algebraMap F E (g.q : F) ∈ M.L.O := by
    rw [M.L.O_def]
    have := isIntegral_algebraMap (R := ↥𝒪[F]) (A := E) (x := g.q)
    convert this using 1
    rw [IsScalarTower.algebraMap_apply (↥𝒪[F]) F E]
    rfl
  set c := algebraMap F E (g.q : F) with hc
  have hcx : ∀ x ∈ Λ₂, c • x ∈ Λ₂ := fun x hx => Λ₂.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  obtain ⟨l, hl, hle⟩ := exists_of_mem_smulLat H hd₁
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₁ (x₁ : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₁ (x₁' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₁ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₁ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hle
  have hap : a ∈ H.perp (H.X t₁.f) := by
    have : a = (x₁ : V) - b := by rw [← hab]; abel
    rw [this]
    exact (H.perp _).sub_mem x₁.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have hap' : a' ∈ H.perp (H.X t₁.f') := by
    have : a' = (x₁' : V) - b' := by rw [← hab']; abel
    rw [this]
    exact (H.perp _).sub_mem x₁'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have haS : a ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha hb (by rw [hab]; exact hx₁L)
  have haS' : a' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha' hb' (by rw [hab']; exact hx₁'L)
  have haS'' : a'' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha'' hb'' (by rw [hab'']; exact hl)
  have hmemG : (θ (ddMk H t₁ ⟨a, haS⟩), θ (ddMk H t₁ ⟨a'', haS''⟩), φ (H.mkW t₁.f ⟨a, hap⟩),
      φ' (H.mkW t₁.f' ⟨a', hap'⟩)) ∈ GamR H t₂ c := by
    rw [← hG]
    exact ⟨_, ⟨⟨a, haS⟩, ⟨a', haS'⟩, ⟨a'', haS''⟩, hap, hap', hda, rfl⟩, rfl⟩
  obtain ⟨u, u', u'', hu, hu', huu, hpe2⟩ := hmemG
  simp only [Prod.mk.injEq] at hpe2
  obtain ⟨e1, e2, e3, e4⟩ := hpe2
  have key : ∀ (m : MMsharp H t₁) (n : MMsharp H t₂) (v : H.W0 t₁.f t₁.f'),
      θ (ddMk H t₁ m) = ddMk H t₂ n → (m : V) + v ∈ t₁.abelian₂ → (n : V) + ↑(ψ v) ∈ Λ₂ := by
    intro m n v hmn hv
    obtain ⟨w, hw1, hw2⟩ := (D.hθ m n).1 hmn
    have h1 : ((v - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
      have : ((v - w : H.W0 t₁.f t₁.f') : V) = ((m : V) + v) - ((m : V) + w) := by
        rw [Submodule.coe_sub]
        abel
      rw [this]
      exact t₁.abelian₂.sub_mem hv hw1
    have h2 := (D.hth (v - w)).1 h1
    have : (n : V) + ↑(ψ v) = ((n : V) + ↑(ψ w)) + ↑(ψ (v - w)) := by
      rw [map_sub, Submodule.coe_sub]
      abel
    rw [this]
    exact Λ₂.add_mem hw2 h2
  have hx₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ Λ₂ :=
    key ⟨a, haS⟩ u ⟨b, hb⟩ e1 (by
      show a + b ∈ _
      rw [hab]
      exact hx₁L)
  have hx₂'' : (u'' : V) + ↑(ψ ⟨b'', hb''⟩) ∈ Λ₂ :=
    key ⟨a'', haS''⟩ u'' ⟨b'', hb''⟩ e2 (by
      show a'' + b'' ∈ _
      rw [hab'']
      exact hl)
  have hbb : (⟨b', hb'⟩ : H.W0 t₁.f t₁.f') = ⟨b, hb⟩ - c • ⟨b'', hb''⟩ :=
    Subtype.ext (by
      show b' = b - c • b''
      rw [← hdb]
      abel)
  have hx₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ Λ₂ := by
    have e : (u' : V) + ↑(ψ ⟨b', hb'⟩) =
        ((u : V) + ↑(ψ ⟨b, hb⟩)) - c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Λ₂.sub_mem hx₂ (hcx _ hx₂'')
  have hp₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ H.perp (H.X t₂.f) :=
    (H.perp _).add_mem hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2)
  have hp₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ H.perp (H.X t₂.f') :=
    (H.perp _).add_mem hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2)
  have hd₂ : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) ∈ H.smulLat c Λ₂ := by
    have e : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) =
        c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hx₂'', rfl⟩
  have hy : a + b ∈ H.perp (H.X t₁.f) := by
    rw [hab]
    exact x₁.2
  have hy' : a' + b' ∈ H.perp (H.X t₁.f') := by
    rw [hab']
    exact x₁'.2
  have hC : φ (H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩) =
      H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := D.hC1 ⟨b, hb⟩
  have hC' : φ' (H.mkW t₁.f' ⟨b', mem_perp_isotropicSpan_of_mem_framePerp' H hb'⟩) =
      H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := D.hC1' ⟨b', hb'⟩
  have hφ : φ (H.mkW t₁.f x₁) = H.mkW t₂.f ⟨_, hp₂⟩ := by
    calc φ (H.mkW t₁.f x₁) = φ (H.mkW t₁.f ⟨a + b, hy⟩) :=
          congrArg φ (mkW_congr H x₁.2 hy hab.symm)
      _ = H.mkW t₂.f ⟨u, hu⟩ + H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := by
          rw [mkW_add H a b hap (mem_perp_isotropicSpan_of_mem_framePerp H hb), map_add (f := _), e3, hC]
      _ = H.mkW t₂.f ⟨_, hp₂⟩ := (mkW_add H _ _ hu _).symm
  have hφ' : φ' (H.mkW t₁.f' x₁') = H.mkW t₂.f' ⟨_, hp₂'⟩ := by
    calc φ' (H.mkW t₁.f' x₁') = φ' (H.mkW t₁.f' ⟨a' + b', hy'⟩) :=
          congrArg φ' (mkW_congr H x₁'.2 hy' hab'.symm)
      _ = H.mkW t₂.f' ⟨u', hu'⟩ + H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := by
          rw [mkW_add H a' b' hap' (mem_perp_isotropicSpan_of_mem_framePerp' H hb'), map_add (f := _), e4, hC']
      _ = H.mkW t₂.f' ⟨_, hp₂'⟩ := (mkW_add H _ _ hu' _).symm
  exact ⟨⟨_, hp₂'⟩, ⟨_, hp₂⟩, hx₂', hx₂, hd₂, Prod.ext hφ' hφ⟩

end RG6

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T2CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ClaimRL (M : Model F E) (r n : ℕ) : Prop := M.split = none → ClaimR M r n

def ClaimRG (M : Model F E) (r n : ℕ) : Prop := M.split.isSome = true → ClaimR M r n

theorem claimR_of_modes (M : Model F E) (r n : ℕ) (hL : ClaimRL M r n) (hG : ClaimRG M r n) :
    ClaimR M r n := by
  rcases hs : M.split with _ | g
  · exact hL hs
  · exact hG (by rw [hs]; rfl)

theorem X_le_span_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩)

theorem X_le_span_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f' ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inr j.castSucc, rfl⟩)

theorem surj_MMsharp (M : Model F E) (hM : M.OK) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {r : ℕ} (t : Term V M r) (hgen : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    ∀ m : ↥(MMsharp H t), ∃ w : ↥(H.W0 t.f t.f'), (m : V) + w ∈ t.abelian₂ := by
  intro m
  have hU' : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam]
    exact hU
  have hmU : (m : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := spanMM_le_U H t m.2.1
  obtain ⟨x, hx, hpx⟩ := ((local_hermitian_glue F E M hM V H t.abelian₂ hgen.1.1 _ hU').1 (m : V) hmU).2
    (fun y hy hyU => m.2.2 y (hgen.2.2.2 y hy (span_frames_le_MM H t hyU)))
  have hx' : x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) ⊔
      H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f'))) := by
    rw [hU'.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
  have hpa : ((Submodule.linearProjOfIsCompl _ _ hU' x :
      ↥(Submodule.span E (Set.range (Sum.elim t.f t.f')))) : V) = a := by
    rw [← hab, map_add (f := _)]
    have e1 := Submodule.projectionOnto_apply_left hU' ⟨a, ha⟩
    have e2 := Submodule.projectionOnto_apply_right hU' ⟨b, hb⟩
    simp only [Submodule.linearProjOfIsCompl] at *
    rw [e1, e2, add_zero]
  have hma : (m : V) = a := by rw [← hpx, hpa]
  have hbW : b ∈ H.W0 t.f t.f' := by rw [hermSp_W0_eq_perp_span_range_MMfam]; exact hb
  refine ⟨⟨b, hbW⟩, ?_⟩
  show (m : V) + b ∈ t.abelian₂
  rw [hma, hab]
  exact hx

theorem claimRL_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRL M r n := by
  intro hs V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hMM₁ : MMo H t₁ ≤ t₁.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
  have hMM₂ : MMo H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) ≤ Λ₂ :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
  have hth' : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂ :=
    fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
  have hθ' : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂ := by
    intro m₁ m₂
    rw [hθ m₁ m₂]
    constructor
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
      exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
    · rintro ⟨w, h1, h2⟩
      exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩
  have hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁

  have hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₁
  have hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₂
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  have hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')), ∃ hu' : u' ∈ H.perp (H.X f₂'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW f₂' ⟨u', hu'⟩ := by
    intro v hv hvp
    rw [← U_swap] at hv
    obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
    rw [U_swap] at hv'
    exact ⟨v', hv', hv'p, e⟩
  have hL := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f f₂ (X_le_span_left H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) φ hC1 hC2
  have hL' := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f' f₂' (X_le_span_right H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) φ' hC1' hC2'
  constructor
  · intro hR
    refine ⟨fun _ => ⟨hL.1 hR.1, hL'.1 hR.2.2.1⟩, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)
  · rintro ⟨h1, -⟩
    obtain ⟨a, b⟩ := h1 hs
    refine ⟨hL.2 a, hyp.2.2.2.2.1, hL'.2 b, hyp.2.2.2.2.2, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)

end T2CR

end Formalism.L2.SG.LsDatumA
end
end
