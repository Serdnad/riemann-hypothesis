module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.MackeyTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IsIrreducibleIff
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open UpperTheory.V.Sd.S2 UpperTheory.V.AlgebraTools UpperTheory.V.Af
open scoped Matrix

section

variable {k : Type} [Field k]

private noncomputable def pX (α β : kˣ) : (Fin 2 → k) →ₗ[k] (Fin 4 → k) where
  toFun a := ![a 1 / β, a 0 / α, -(a 1 / β), a 0 / α]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

private noncomputable def pY : (Fin 2 → k) →ₗ[k] (Fin 4 → k) where
  toFun b := ![b 1, -b 0, b 1, b 0]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp

private theorem pX_apply (α β : kˣ) (a : Fin 2 → k) : pX α β a = ![a 1 / β, a 0 / α, -(a 1 / β), a 0 / α] := rfl

private theorem pY_apply (b : Fin 2 → k) : pY b = ![b 1, -b 0, b 1, b 0] := rfl

private theorem pX_inj (α β : kˣ) : Function.Injective (pX α β) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [pX_apply] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

private theorem pY_inj : Function.Injective (pY (k := k)) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 3
  simp [pY_apply] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

private theorem mix_pX (h2 : (2 : k) ≠ 0) (α β : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) (a : Fin 2 → k) :
    mix (β / α) A B *ᵥ pX α β a = pX α β (A *ᵥ a) := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  ext i
  fin_cases i <;>
    simp [mix, pX_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem mix_pY (h2 : (2 : k) ≠ 0) (γ : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) (a : Fin 2 → k) :
    mix γ A B *ᵥ pY a = pY (B *ᵥ a) := by
  have hγ := γ.ne_zero
  ext i
  fin_cases i <;>
    simp [mix, pY_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem diag_pX (α β : kˣ) (a : Fin 2 → k) :
    Matrix.diagonal ![(β : k), -(α : k), -(β : k), (α : k)] *ᵥ pX α β a = pY a := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  ext i
  fin_cases i <;> simp [pX_apply, pY_apply, Matrix.mulVec_diagonal] <;> field_simp

private theorem compl_XY (h2 : (2 : k) ≠ 0) (α β : kˣ) :
    IsCompl (LinearMap.range (pX α β)) (LinearMap.range (pY (k := k))) := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    have h2' := congrFun hb 2
    have h3 := congrFun hb 3
    simp [pX_apply, pY_apply] at h0 h1 h2' h3
    have e1 : b 1 = 0 := mul_left_cancel₀ h2 (by linear_combination h0 + h2')
    have e0 : b 0 = 0 := mul_left_cancel₀ h2 (by linear_combination h3 - h1)
    rw [← hb]
    ext i; fin_cases i <;> simp [pY_apply, e0, e1]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨_, ⟨![α * (v 1 + v 3) / 2, β * (v 0 - v 2) / 2], rfl⟩, _,
      ⟨![(v 3 - v 1) / 2, (v 0 + v 2) / 2], rfl⟩, ?_⟩
    ext i; fin_cases i <;> simp [pX_apply, pY_apply] <;> field_simp <;> ring

private theorem gl_surj (g : GL (Fin 2) k) (b : Fin 2 → k) : ∃ a, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ a = b :=
  ⟨((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ b, by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

end

theorem UpperTheory.mix_invariant_plane_decomposition :
    UpperTheory.V.Sd.S2.MixIrr := by
  intro k Γ₀ Γ _ _ _ j t α β ρ R hm U hU hirr hne
  have hi := hm.index
  have hcj : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := by
    intro h
    have : t⁻¹ * j h * t ∈ j.range := by
      rw [mul_assoc]
      simp only [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff, hm.nmem]
      simp
    exact this
  have hX : ∀ h a, (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a = pX α β ((ρ h : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro h a
    obtain ⟨h', e⟩ := hcj h
    rw [hm.on h h' e, mix_pX hm.two]
  have hY : ∀ h h', j h' = t⁻¹ * j h * t → ∀ a,
      (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pY a = pY ((ρ h' : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro h h' e a
    rw [hm.on h h' e, mix_pY hm.two]
  obtain ⟨s, hsU, hs⟩ := SetLike.not_le_iff_exists.1 hU
  obtain ⟨h₀, hh₀⟩ : s * t⁻¹ ∈ j.range := by
    simp only [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff, hm.nmem, hs]
  obtain ⟨h₀', e₀⟩ := hcj h₀
  have hsX : ∀ a, (R s : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a = pY ((ρ h₀' : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro a
    have : s = j h₀ * t := by rw [hh₀]; group
    rw [this, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hm.off, diag_pX, hY h₀ h₀' e₀]
  have hmap : (LinearMap.range (pX α β)).map (matRep (R.comp U.subtype) ⟨s, hsU⟩) = LinearMap.range (pY (k := k)) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, (hsX a).symm⟩
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := gl_surj (ρ h₀') b
      exact ⟨_, ⟨a, rfl⟩, hsX a⟩
  have key := mackeyTwo (matRep (R.comp U.subtype)) (j.range.subgroupOf U) ⟨s, hsU⟩ (LinearMap.range (pX α β))
    ?_ hs ?_ ?_ ?_ ?_
  · refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => key W fun g _ v hv => hW g v hv⟩
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsU⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mul_mem_iff_of_index_two hi, hs]
    by_cases hb : (b : Γ) ∈ j.range <;> simp [hb]
  · rintro ⟨g, hg⟩ ⟨h, rfl : j h = g⟩ _ ⟨a, rfl⟩
    exact ⟨_, (hX h a).symm⟩
  · intro W hle hW
    rcases hirr.2.2 (W.comap (pX α β)) le_top (by
      rintro ⟨h, hh⟩ a ha
      have := hW ⟨j h, hh⟩ ⟨h, rfl⟩ _ ha
      change (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a ∈ W at this
      rw [hX] at this
      exact this) with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨a, rfl⟩ := hle hw
      have : a ∈ W.comap (pX α β) := hw
      rw [h0, Submodule.mem_bot] at this
      simp [this]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨a, rfl⟩
      have : a ∈ W.comap (pX α β) := by rw [h0]; trivial
      exact this
  · rw [hmap]; exact compl_XY hm.two α β
  · rw [hmap]
    rintro ⟨e, he⟩
    let f : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) :=
      (LinearEquiv.ofInjective _ (pX_inj α β)).trans (e.trans (LinearEquiv.ofInjective _ pY_inj).symm)
    have hf : ∀ a, pY (f a) = e ⟨pX α β a, a, rfl⟩ := by
      intro a
      have := congrArg Subtype.val ((LinearEquiv.ofInjective _ (pY_inj (k := k))).apply_symm_apply (e ⟨pX α β a, a, rfl⟩))
      exact this
    let M : GL (Fin 2) k :=
      ⟨LinearMap.toMatrix' (f : (Fin 2 → k) →ₗ[k] (Fin 2 → k)), LinearMap.toMatrix' (f.symm : (Fin 2 → k) →ₗ[k] (Fin 2 → k)),
        by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
    have hM : ∀ a, (M : Matrix (Fin 2) (Fin 2) k) *ᵥ a = f a := by
      intro a
      simp [M, LinearMap.toMatrix'_mulVec]
    refine hne ⟨M, fun h h' hh e' => ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro a
    simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hM]
    apply pY_inj
    rw [← hY h h' e', hf, hf]
    exact (he ⟨j h, hh⟩ ⟨h, rfl⟩ ⟨pX α β a, a, rfl⟩ ⟨_, _, rfl⟩ (hX h a).symm).symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws UpperTheory.V.Sd

private theorem closed_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F E : IntermediateField ℚ Ω) :
    IsClosed ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) := by
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) =
      ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rfl
  rw [e]
  exact isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)

private theorem lim_pt {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (S : Set Γ) (hS : IsClosed S) (g : Γ)
    (hg : (l : ℤ_[l]) ∣ (ε g : ℤ_[l]) - 1) (hm : ∀ n : ℕ, g ^ l ^ n ∈ S) : ∃ h ∈ S, ε h = 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have h2 := dvd_sub_pow_of_dvd_sub hg n
    rw [one_pow] at h2
    have h3 := (pow_dvd_pow _ n.le_succ).trans h2
    rw [map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h3
  obtain ⟨h, hh, hc⟩ := hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))
  refine ⟨h, hh, Units.ext ?_⟩
  have hc' := hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt
  exact eq_of_nhds_neBot (hc'.clusterPt.mono ht)

private theorem dvd_of_om {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.om g = 1) : (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - 1 := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  have h := hD.om_bar g
  simp only [Raw.bar, hg, Units.val_one] at h
  have h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0 := by
    rw [map_sub, map_sub, map_one, h, sub_eq_zero]
    rfl
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := fun hu => h1 (hu.map _)
  rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  (T : Tower D)

private noncomputable def eta : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt wPs)

private theorem eta_val (g : G T.F Ω) : (eta T g : ResidueField c.O) = T.rb wPs g := rfl

private theorem eta_sq (hT : T.Two) (g : G T.F Ω) : eta T g ^ 2 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, eta_val, hT.sq, Units.val_one])

private theorem eta_om (hD : D.Good) (hT : T.Two) (hne : ∀ g ∈ T.G', T.rb wPs g = 1) (g : G T.F Ω) (hg' : g ∈ T.GalL)
    (hg : D.om (resQ T.F g) = 1) : eta T g = 1 := by
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  obtain ⟨k₀, -, -, -, hk⟩ := hT.quad
  have hk' : ∀ g, eta T g = 1 ↔ g ∈ k₀.fixingSubgroup.comap (resQ T.F) := fun g => by
    rw [Subgroup.mem_comap, ← hk, ← eta_val, Units.val_eq_one]
  have hc : Continuous fun h : G T.F Ω => g⁻¹ * h := continuous_const_mul _
  have h0 : IsClosed (T.GalL : Set (G T.F Ω)) := closed_fix T.F T.K
  have hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1 := dvd_of_om D hD (resQ T.F g) hg
  obtain ⟨h, ⟨h1, h2⟩, h3⟩ := lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _
    (h0.inter ((closed_fix T.F k₀).preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by
      refine (hk' _).1 ?_
      obtain ⟨m, hm⟩ := (hl.out.odd_of_ne_two hD.l_odd).pow (n := n)
      rw [map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, eta_sq T hT, one_pow, one_mul, inv_mul_cancel]⟩)
  have h4 : eta T h = 1 := by
    rw [← Units.val_eq_one, eta_val]
    exact hne h ⟨h1, h3⟩
  have h5 := (hk' _).2 h2
  rwa [map_mul, h4, mul_one, map_inv, inv_eq_one] at h5

private theorem eta_mul (g : G T.F Ω) :
    eta T g * Raw.bar (chi D T.pr 2) (resQ T.F g) = Raw.bar (chi D T.pr 0) (resQ T.F g) ∧
    eta T g * Raw.bar (chi D T.pr 3) (resQ T.F g) = Raw.bar (chi D T.pr 1) (resQ T.F g) := by
  have e : (T.fr ∅).rt wPs g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹ := by
    show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (0 : ℤ) *
      (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (1 : ℤ) = _
    rw [zpow_zero, zpow_one, one_mul]
  have e' : (T.fr ∅).rt wPs g = chi D T.pr 1 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹ := by
    rw [e]
    generalize resQ T.F g = s
    cases T.pr
    · show D.al s * D.Psi s * (D.al s)⁻¹ = D.Psi s * 1⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_comm]
    · show D.al s * (D.al s * D.Psi s)⁻¹ = 1 * (D.Psi s)⁻¹
      rw [one_mul, mul_inv, mul_inv_cancel_left]
  rw [eta_val]
  constructor
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]

private theorem eta_mul' (hT : T.Two) (g : G T.F Ω) {u v : ResidueField c.O} (h : eta T g * u = v) : eta T g * v = u := by
  rw [← h, ← mul_assoc, ← Units.val_mul, ← pow_two, eta_sq T hT, Units.val_one, one_mul]

private noncomputable def etaL : T.GalL →* (ResidueField c.O)ˣ := (eta T).comp T.GalL.subtype

private theorem etaL_app (g : T.GalL) : etaL T g = eta T g := rfl

private theorem etaL_sq (hT : T.Two) : etaL T ^ 2 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, eta_sq T hT]

private theorem etaL_perm (hT : T.Two) (i : Fin 4) : ∃ j, ∀ g : T.GalL, etaL T g * Raw.bar (chi D T.pr i) (resQ T.F g) =
      Raw.bar (chi D T.pr j) (resQ T.F g) := by
  simp only [etaL_app]
  match i with
  | 0 => exact ⟨2, fun g => eta_mul' T hT g (eta_mul T g).1⟩
  | 1 => exact ⟨3, fun g => eta_mul' T hT g (eta_mul T g).2⟩
  | 2 => exact ⟨0, fun g => (eta_mul T g).1⟩
  | 3 => exact ⟨1, fun g => (eta_mul T g).2⟩

end

theorem UpperTheory.residual_characters_psi_ne :
    UpperTheory.V.Sd.S2.PsiNe := by
  intro Ω _ _ _ l hl c D T hD hO hT
  by_contra hne
  have hne' : ∀ g ∈ T.G', T.rb wPs g = 1 := fun g hg => by_contra fun h => hne ⟨g, hg, h⟩
  have key := hO.g3' (etaL T) (etaL_sq T hT)
    (fun g hg => by rw [etaL_app]; exact eta_om T hD hT hne' g g.2 hg) (etaL_perm T hT)
  obtain ⟨g, hg, hg'⟩ := hO.g3 wPs (by decide)
  have h1 := etaL_app T ⟨g, hg⟩
  rw [key, MonoidHom.one_apply] at h1
  apply hg'
  rw [← eta_val, ← h1, Units.val_one]
end

section

noncomputable section

open UpperTheory.V.Sd.S2 ReciprocityTheory.Gal

namespace UpperTheory

private theorem mix_cont {k X : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace X] (γ : kˣ)
    {A B : X → Matrix (Fin 2) (Fin 2) k} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => mix γ (A x) (B x) := by
  have a : ∀ i j, Continuous fun x => A x i j := fun i j => hA.matrix_elem i j
  have b : ∀ i j, Continuous fun x => B x i j := fun i j => hB.matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mix, div_eq_mul_inv] <;> fun_prop

theorem continuous_mix_family : UpperTheory.V.Sd.S2.MixCont := by
  intro l _ Γ₀ Γ _ _ _ _ _ j t α β ρ R hM hj hρ
  haveI hN : j.range.Normal := Subgroup.normal_of_index_eq_two hM.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem (j h) ⟨h, rfl⟩ t⁻¹
    simpa using this
  choose c hc using hc
  have cc : Continuous c := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ c) = fun h => t⁻¹ * j h * t := funext hc
    rw [this]
    have := hj.continuous
    fun_prop
  have ci : Continuous fun h : Γ₀ => h⁻¹ := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ fun h : Γ₀ => h⁻¹) = fun h => (j h)⁻¹ := funext fun h => by simp
    rw [this]
    exact hj.continuous.inv
  have hv : Continuous fun h => (ρ h).val := Units.continuous_val.comp hρ
  have h1 : Continuous fun h => (R (j h)).val := by
    have : (fun h => (R (j h)).val) = fun h => mix (β / α) (ρ h) (ρ (c h)) :=
      funext fun h => hM.on h (c h) (hc h)
    rw [this]
    exact mix_cont _ hv (hv.comp cc)
  have h2 : Continuous (R ∘ j) := by
    rw [Units.continuous_iff]
    refine ⟨h1, ?_⟩
    have := h1.comp ci
    refine this.congr fun h => ?_
    simp only [Function.comp, map_inv]
  refine continuous_of_continuousAt_one R ?_
  have := (hj.continuousAt_iff (g := R) (x := 1)).1 h2.continuousAt
  rwa [map_one] at this

end UpperTheory
end
end

section

open Matrix UpperTheory.V.Af

private theorem schur2 {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] (ρ : G →* GL (Fin 2) κ)
    (h : IsIrr ρ) (N : Matrix (Fin 2) (Fin 2) κ)
    (hN : ∀ g, N * (ρ g : Matrix (Fin 2) (Fin 2) κ) = (ρ g : Matrix (Fin 2) (Fin 2) κ) * N) : ∃ x : κ, N = x • 1 := by
  obtain ⟨x, hx⟩ := Module.End.exists_eigenvalue (Matrix.toLin' N)
  have htop : Module.End.eigenspace (Matrix.toLin' N) x = ⊤ := by
    refine (h.2.2 _ le_top fun g v hv => ?_).resolve_left hx
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hN g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  refine ⟨x, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have : v ∈ Module.End.eigenspace (Matrix.toLin' N) x := by rw [htop]; trivial
  rw [Module.End.mem_eigenspace_iff.1 this]
  simp

theorem UpperTheory.mix_sign_twist :
    UpperTheory.V.Sd.S2.SignTw := by
  intro k Γ _ _ _ ρ ρ' H' M hirr hM s hs hdet
  set N : GL (Fin 2) k := (ρ s)⁻¹ * (M⁻¹ * ρ' s * M) with hN
  have hcomm : ∀ h ∈ H', N * ρ h = ρ h * N := by
    intro h hh
    have e1 := hM h hh
    have e2 := hM _ (hs h hh)
    simp only [map_mul, map_inv, e1] at e2
    have e3 : ρ' s * (M * ρ h * M⁻¹) = M * (ρ s * ρ h * (ρ s)⁻¹) * M⁻¹ * ρ' s := by
      rw [← e2]; group
    calc N * ρ h = (ρ s)⁻¹ * M⁻¹ * (ρ' s * (M * ρ h * M⁻¹)) * M := by rw [hN]; group
      _ = ρ h * N := by rw [e3, hN]; group
  obtain ⟨x, hx⟩ := schur2 _ hirr (N : Matrix (Fin 2) (Fin 2) k) (fun g => by
    have := congrArg Units.val (hcomm g g.2)
    simpa using this)
  have hd : Matrix.GeneralLinearGroup.det N = 1 := by
    rw [hN]
    simp only [map_mul, map_inv, hdet]
    rw [mul_right_comm, inv_mul_cancel, one_mul, inv_mul_cancel]
  have hx2 : x * x = 1 := by
    have h1 : (N : Matrix (Fin 2) (Fin 2) k).det = 1 := congrArg Units.val hd
    rw [hx] at h1
    simpa [pow_two] using h1
  have hc : ∀ A : GL (Fin 2) k, N * A = A * N := fun A => Units.ext (by simp [hx])
  have hNN : N * N = 1 := Units.ext (by simp [hx, smul_smul, hx2])
  have e : ρ' s = M * (ρ s * N) * M⁻¹ := by rw [hN]; group
  clear_value N
  rw [map_mul, map_mul, e]
  calc M * (ρ s * N) * M⁻¹ * (M * (ρ s * N) * M⁻¹) = M * (ρ s * (N * ρ s) * N) * M⁻¹ := by group
    _ = M * (ρ s * ρ s * (N * N)) * M⁻¹ := by rw [hc]; simp only [mul_assoc]
    _ = _ := by rw [hNN, mul_one]
end
