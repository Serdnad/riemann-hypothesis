module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle001
public import Mathlib.Algebra.DirectSum.LinearMap
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle005
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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

theorem UpperTheory.V.Z.Sym.Tf.formsFin :
    UpperTheory.V.Z.Sym.Tf.FormsFin := by
  intro Γ G V _ _ _ _ _ B hB
  obtain ⟨S, hS⟩ := hB.cls
  let L : B.Forms →ₗ[ℂ] (S → V) :=
    (LinearMap.funLeft ℂ V (fun s : S => (s : G))).comp B.Forms.subtype
  refine Module.Finite.of_injective L ?_
  intro φ ψ h
  apply Subtype.ext
  funext g
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
  have hsv : φ.1 s = ψ.1 s := congrFun h ⟨s, hs⟩
  have e1 : φ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • φ.1 (B.ι γ * s) := φ.2.2 _ ⟨u, hu⟩
  have e2 : ψ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • ψ.1 (B.ι γ * s) := ψ.2.2 _ ⟨u, hu⟩
  have f1 : φ.1 (B.ι γ * s) = B.W γ (φ.1 s) := φ.2.1 γ s
  have f2 : ψ.1 (B.ι γ * s) = B.W γ (ψ.1 s) := ψ.2.1 γ s
  rw [e1, e2, f1, f2, hsv]
end

section

open UpperTheory.V.Z.Sym MulAction in
theorem UpperTheory.V.Z.Sym.Tf.orbReps :
    UpperTheory.V.Z.Sym.Tf.OrbReps := by
  classical
  intro T G _ _ ι C θ U f δ hf hδ J S x hx hs
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  have sm : ∀ (t : T) (g : G), t • (g : G ⧸ U) = ((ι t * g : G) : G ⧸ U) := fun _ _ => rfl
  have k1 : ∀ (t : T) (g : G), ∀ u ∈ U, f ((ι t * g * u)⁻¹ * δ * θ (ι t * g * u)) = f (g⁻¹ * δ * θ g) := fun t g u hu => by
    rw [← hf u hu (g⁻¹ * δ * θ g)]
    congr 1
    conv_rhs => rw [← hδ t]
    simp [mul_assoc]
  have st : ∀ (t : T) (y : G ⧸ U), stabilizer T (t • y) = stabilizer T y := fun t y => by
    ext a
    simp only [mem_stabilizer_iff]
    rw [smul_smul, mul_comm, mul_smul, smul_left_cancel_iff]
  let q : J → orbitRel.Quotient T (G ⧸ U) := fun i => Quotient.mk'' (x i : G ⧸ U)
  have rel : ∀ (o : orbitRel.Quotient T (G ⧸ U)) (i : J), o = q i ↔ ∃ t, ∃ u ∈ U, o.out.out = ι t * x i * u := fun o i => by
    constructor
    · intro h
      have : orbitRel T _ o.out (x i : G ⧸ U) := Quotient.exact (by rw [Quotient.out_eq]; exact h)
      obtain ⟨t, ht⟩ := this
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (ι t * x i)
      exact ⟨t, u, u.2, by rw [← hu, ← sm]; exact congrArg _ ht.symm⟩
    · rintro ⟨t, u, hu, h⟩
      rw [← o.out_eq]
      refine Quotient.sound ⟨t, ?_⟩
      show t • _ = _
      rw [sm, ← o.out.out_eq', h]
      exact (QuotientGroup.mk_mul_of_mem _ hu).symm
  unfold orb wcount
  rw [finsum_eq_sum_of_support_subset (s := S.image q) _ fun o ho => ?_, Finset.sum_image fun i hi j hj h => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨t, u, hu, h⟩ := (rel (q i) i).1 rfl
    have e : (q i).out = t • (x i : G ⧸ U) := by
      rw [sm, ← (q i).out.out_eq', h]; exact QuotientGroup.mk_mul_of_mem _ hu
    beta_reduce
    rw [h, k1 t _ u hu, e, st]
    rfl
  · obtain ⟨t, u, hu, h1⟩ := (rel (q i) i).1 rfl
    obtain ⟨t', u', hu', h2⟩ := (rel (q i) j).1 h
    refine hx i hi j hj (t'⁻¹ * t) (u * u'⁻¹) (mul_mem hu (inv_mem hu')) ?_
    have := h1.symm.trans h2
    rw [map_mul, map_inv, mul_assoc (ι t')⁻¹, mul_assoc (ι t')⁻¹, ← mul_assoc _ u, this]
    simp [mul_assoc]
  · obtain ⟨t, i, hi, u, hu, h⟩ := hs o.out.out (right_ne_zero_of_mul ho)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, hi, ((rel o i).2 ⟨t, u, hu, h⟩).symm⟩)
end

section

open UpperTheory.V.Z.Sym in
theorem UpperTheory.V.Z.Sym.Tf.centFin :
    UpperTheory.V.Z.Sym.Tf.CentFin := by
  intro Γ G V _ _ _ _ B hB tw f hf δ
  classical
  obtain ⟨S₀, hS₀⟩ := hB.cls
  choose D hD using fun g : G => UpperTheory.V.Z.Sym.Tf.finD B hB tw f hf g g
  let rep : G → Γ → Γ := fun g d =>
    if h : ∃ γ : Γ, ∃ z ∈ B.Γ₀, γ⁻¹ * δ * tw.θΓ γ = d * z then h.choose else 1
  have rep_spec : ∀ g d, (∃ γ : Γ, ∃ z ∈ B.Γ₀, γ⁻¹ * δ * tw.θΓ γ = d * z) →
      ∃ z ∈ B.Γ₀, (rep g d)⁻¹ * δ * tw.θΓ (rep g d) = d * z := by
    intro g d h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨S₀.biUnion (fun g => (D g).image (fun d => B.ι (rep g d) * g)), ?_⟩
  intro y hy
  obtain ⟨γ, g, hg, u, hu, rfl⟩ := hS₀ y
  have hcomm : ∀ c : Γ, tw.θ (B.ι c) = B.ι (tw.θΓ c) := tw.comm
  have expand : (B.ι γ * g * u)⁻¹ * B.ι δ * tw.θ (B.ι γ * g * u) =
      u⁻¹ * (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g) * tw.θ u := by
    simp only [map_mul, map_inv, hcomm]
    group
  have hne : f (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g) ≠ 0 := by
    intro h0
    apply hy
    show f ((B.ι γ * g * u)⁻¹ * B.ι δ * tw.θ (B.ι γ * g * u)) = 0
    rw [expand]
    have e1 := hf.right ⟨u, hu⟩ (u⁻¹ * (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g))
    have e2 := hf.left ⟨u⁻¹, B.U.inv_mem hu⟩ (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g)
    simp only at e1 e2
    rw [e1, e2, h0, mul_zero, mul_zero]
  obtain ⟨d, hd, z₂, hz₂, hγ⟩ := hD g (γ⁻¹ * δ * tw.θΓ γ) hne
  obtain ⟨z₁, hz₁, hr⟩ := rep_spec g d ⟨γ, z₂, hz₂, hγ⟩
  set r := rep g d with hr_def
  have hdr : d = r⁻¹ * δ * tw.θΓ r * z₁⁻¹ := eq_mul_inv_of_mul_eq hr.symm
  have hc : z₁⁻¹ * z₂ ∈ Subgroup.center Γ :=
    B.cenΓ (B.Γ₀.mul_mem (B.Γ₀.inv_mem hz₁) hz₂)
  have hx : γ * r⁻¹ ∈ tw.Cent δ := by
    refine ⟨z₁⁻¹ * z₂, B.Γ₀.mul_mem (B.Γ₀.inv_mem hz₁) hz₂, ?_⟩
    calc (γ * r⁻¹)⁻¹ * δ * tw.θΓ (γ * r⁻¹)
        = r * (γ⁻¹ * δ * tw.θΓ γ) * (tw.θΓ r)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = r * (d * z₂) * (tw.θΓ r)⁻¹ := by rw [hγ]
      _ = δ * (tw.θΓ r * (z₁⁻¹ * z₂)) * (tw.θΓ r)⁻¹ := by
          rw [hdr]
          group
      _ = δ * ((z₁⁻¹ * z₂) * tw.θΓ r) * (tw.θΓ r)⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp hc (tw.θΓ r)).symm]
      _ = δ * (z₁⁻¹ * z₂) := by group
  refine ⟨⟨γ * r⁻¹, hx⟩, B.ι r * g, ?_, u, hu, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
  · show B.ι γ * g * u = B.ι (γ * r⁻¹) * (B.ι r * g) * u
    rw [map_mul, map_inv]
    group
end

section

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

private lemma exists_ker_of_pow {M : Type} [AddCommGroup M] [Module ℂ M] (N : Module.End ℂ M) (W : Submodule ℂ M)
    (hW : ∀ w ∈ W, N w ∈ W) : ∀ (k : ℕ) (v : M), v ∈ W → v ≠ 0 → (N ^ k) v = 0 → ∃ w ∈ W, w ≠ 0 ∧ N w = 0 := by
  intro k
  induction k with
  | zero => intro v _ hv h; exact absurd (by simpa using h) hv
  | succ k ih =>
    intro v hvW hv h
    by_cases h0 : N v = 0
    · exact ⟨v, hvW, hv, h0⟩
    · exact ih (N v) (hW v hvW) h0 (by rw [pow_succ] at h; exact h)

theorem eigVec : EigVec := by
  intro Λ M _ _ _ u hc χ
  constructor
  · intro h
    set E : Submodule ℂ M := ⨅ a, (u a).maxGenEigenspace (χ a) with hE
    let S : Set (Submodule ℂ M) := {W | W ≠ ⊥ ∧ W ≤ E ∧ ∀ b, ∀ w ∈ W, u b w ∈ W}
    have hS : S.Nonempty := by
      refine ⟨E, h, le_rfl, fun b w hw => ?_⟩
      rw [hE, Submodule.mem_iInf] at hw ⊢
      intro a
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc a b) (χ a) (hw a)
    obtain ⟨W, ⟨hW0, hWE, hWs⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ M)).has_min S hS
    obtain ⟨v, hvW, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    refine ⟨v, hv, fun a => ?_⟩
    have key : W ⊓ (u a).eigenspace (χ a) ∈ S := by
      refine ⟨?_, inf_le_left.trans hWE, fun b w hw => ⟨hWs b w hw.1, ?_⟩⟩
      · have hva : v ∈ (u a).maxGenEigenspace (χ a) := by
          have := hWE hvW
          rw [hE, Submodule.mem_iInf] at this
          exact this a
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hva
        obtain ⟨w, hwW, hw, hN⟩ := exists_ker_of_pow (u a - χ a • (1 : Module.End ℂ M)) W
          (fun w hw => by
            simpa using W.sub_mem (hWs a w hw) (W.smul_mem (χ a) hw)) k v hvW hv hk
        refine (Submodule.ne_bot_iff _).2 ⟨w, ⟨hwW, ?_⟩, hw⟩
        refine Module.End.mem_eigenspace_iff.2 ?_
        simpa [sub_eq_zero] using hN
      · have h2 := Module.End.mem_eigenspace_iff.1 hw.2
        refine Module.End.mem_eigenspace_iff.2 ?_
        have h3 : u a (u b w) = u b (u a w) := congrArg (fun f : Module.End ℂ M => f w) (hc a b).eq
        rw [h3, h2, map_smul]
    have heq : W ⊓ (u a).eigenspace (χ a) = W := by
      by_contra hne
      exact hmin _ key (lt_of_le_of_ne inf_le_left hne)
    rw [← heq] at hvW
    exact Module.End.mem_eigenspace_iff.1 hvW.2
  · rintro ⟨v, hv, h⟩
    refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv⟩
    rw [Submodule.mem_iInf]
    intro a
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp [h a]⟩

end UpperTheory.V.Z.Sym.Tf
end
end

section

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

section

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V} {s : B.Tw} {f : G → ℂ}

private theorem rep_indep (hf : s.IsTest f) (φ : B.Forms) (h y : G) :
    f (s.θ (y : G ⧸ B.U).out) • s.Θ (φ.1 (h * (y : G ⧸ B.U).out)) = f (s.θ y) • s.Θ (φ.1 (h * y)) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U y
  rw [hu, map_mul, hf.right, ← mul_assoc, φ.2.2, map_smul, smul_smul, mul_right_comm,
    Units.inv_mul, one_mul]

private theorem fin_supp (hf : s.IsTest f) (k : G ⧸ B.U → V) :
    (Function.support fun x : G ⧸ B.U => f (s.θ x.out) • k x).Finite := by
  refine hf.fin.subset fun x hx => ?_
  rw [Function.mem_support] at hx
  rw [Set.mem_setOf_eq]
  intro h0
  exact hx (by rw [h0, zero_smul])

private theorem opF_mem (hf : s.IsTest f) (φ : B.Forms) : s.opF f φ.1 ∈ B.Forms := by
  refine ⟨fun γ g => ?_, fun g u => ?_⟩
  · unfold Base.Tw.opF
    have hθ : s.θ.symm (B.ι γ) = B.ι (s.θΓ.symm γ) := by
      rw [MulEquiv.symm_apply_eq, s.comm, MulEquiv.apply_symm_apply]
    have key : B.W γ (∑ᶠ x : G ⧸ B.U, f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)))
        = ∑ᶠ x : G ⧸ B.U, B.W γ (f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out))) :=
      (B.W γ).toAddMonoidHom.map_finsum (fin_supp hf _)
    rw [key]
    refine finsum_congr fun x => ?_
    rw [map_smul, map_mul, hθ, mul_assoc, φ.2.1, s.int, MulEquiv.apply_symm_apply]
  · unfold Base.Tw.opF
    rw [smul_finsum' _ (fin_supp hf _)]
    let e : Equiv.Perm (G ⧸ B.U) := MulAction.toPerm ((s.θ.symm (u : G))⁻¹)
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun x => ?_
    have hex : e x = (((s.θ.symm (u : G))⁻¹ * x.out : G) : G ⧸ B.U) := by
      show (s.θ.symm (u : G))⁻¹ • x = _
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rw [hex, rep_indep hf φ (s.θ.symm (g * u)) ((s.θ.symm (u : G))⁻¹ * x.out)]
    have hg : s.θ.symm (g * ↑u) * ((s.θ.symm (u : G))⁻¹ * x.out) = s.θ.symm g * x.out := by
      rw [map_mul, mul_assoc, mul_inv_cancel_left]
    have hf1 : f (s.θ ((s.θ.symm (u : G))⁻¹ * x.out)) = (B.ω u : ℂ) * f (s.θ x.out) := by
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
      have hl := hf.left u⁻¹ (s.θ x.out)
      simp only [Subgroup.coe_inv, InvMemClass.coe_inv] at hl
      rw [hl, map_inv, inv_inv]
    rw [hg, hf1, mul_smul]

private def opL (hf : s.IsTest f) : Module.End ℂ B.Forms where
  toFun φ := ⟨s.opF f φ.1, opF_mem hf φ⟩
  map_add' φ ψ := by
    refine Subtype.ext (funext fun g => ?_)
    change s.opF f (φ.1 + ψ.1) g = s.opF f φ.1 g + s.opF f ψ.1 g
    unfold Base.Tw.opF
    rw [← finsum_add_distrib (fin_supp hf _) (fin_supp hf _)]
    refine finsum_congr fun x => ?_
    rw [Pi.add_apply, map_add (f := _), smul_add]
  map_smul' c φ := by
    refine Subtype.ext (funext fun g => ?_)
    change s.opF f (c • φ.1) g = c • s.opF f φ.1 g
    unfold Base.Tw.opF
    rw [smul_finsum' _ (fin_supp hf _)]
    refine finsum_congr fun x => ?_
    rw [Pi.smul_apply, map_smul, smul_comm]

end

theorem rSpec : RSpec := by
  intro Γ G V _ _ _ _ B s f hf φ
  have h : ∃ L : Module.End ℂ B.Forms, ∀ φ, (L φ).1 = s.opF f φ.1 := ⟨opL hf, fun _ => rfl⟩
  unfold Base.Tw.R
  rw [dite_eq_left h]
  exact h.choose_spec φ

end UpperTheory.V.Z.Sym.Tf
end
end

section

open Module in
theorem UpperTheory.V.Z.Sym.Tf.trPos :
    UpperTheory.V.Z.Sym.Tf.TrPos := by
  intro Λ M _ _ _ u hc
  classical
  have hint := UpperTheory.V.Z.Sym.Tf.Vg_int (u := u) hc
  have hfin : {χ | UpperTheory.V.Z.Sym.Tf.Vg u χ ≠ ⊥}.Finite := by
    have := (UpperTheory.V.Z.Sym.Tf.Vg_indep hc).fintypeNeBotOfFiniteDimensional
    exact Set.finite_coe_iff.mp (@Finite.of_fintype _ this)
  refine ⟨hfin.toFinset, fun χ => Module.finrank ℂ (UpperTheory.V.Z.Sym.Tf.Vg u χ), ?_, ?_, ?_⟩
  · intro χ
    simp [Set.Finite.mem_toFinset, UpperTheory.V.Z.Sym.IsGenEig]
  · intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    exact Submodule.one_le_finrank_iff.mpr hχ
  · intro a
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (fun χ => UpperTheory.V.Z.Sym.Tf.Vg_maps hc a χ)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have h1 : Set.MapsTo ⇑(1 : Module.End ℂ M) ↑(UpperTheory.V.Z.Sym.Tf.Vg u χ) ↑(UpperTheory.V.Z.Sym.Tf.Vg u χ) :=
      fun v hv => hv
    have key := UpperTheory.V.Z.Sym.Tf.trace_Vg hc χ 1 id h1 (fun b v _ => by simp) (fun b => rfl) a
      (by simpa using UpperTheory.V.Z.Sym.Tf.Vg_maps hc a χ)
    simp only [mul_one] at key
    rw [key]
    have h2 : LinearMap.restrict (1 : Module.End ℂ M) h1 = 1 := by
      ext v
      rfl
    rw [h2, LinearMap.trace_one, mul_comm]
end

section

private theorem artin {P : Type} [Mul P] (T : Finset (P → ℂ)) : ∀ c : (P → ℂ) → ℂ,
    (∀ χ ∈ T, χ ≠ 0 ∧ ∀ p q, χ (p * q) = χ p * χ q) → (∀ p, ∑ χ ∈ T, c χ * χ p = 0) → ∀ χ ∈ T, c χ = 0 :=
  _root_.UpperTheory.Reformulated.B.Qh30.artin T

private theorem grp {P I : Type} [DecidableEq (P → ℂ)] (S : Finset I) (a : I → ℂ) (α : I → P → ℂ) (T : Finset (P → ℂ))
    (h : ∀ i ∈ S, α i ≠ 0 → α i ∈ T) (p : P) :
    ∑ χ ∈ T, (∑ i ∈ S.filter (fun i => α i = χ), a i) * χ p = ∑ i ∈ S, a i * α i p := by
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases h0 : α i = 0
  · rw [h0]; simp only [Pi.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun χ _ => ?_
    split_ifs with e
    · subst e; simp
    · simp
  · rw [Finset.sum_eq_single (α i) (fun χ _ e => by simp [e.symm]) fun e => absurd (h i hi h0) e]; simp

theorem UpperTheory.V.Z.Sym.Tf.extract :
    UpperTheory.V.Z.Sym.Tf.Extract := by
  classical
  intro P I J _ S S' a b α β hα hβ h χ hχ hb
  by_contra hn
  push Not at hn
  set T := (S.image α ∪ S'.image β).filter (· ≠ 0) with hT
  have key := artin T (fun χ => ∑ i ∈ S.filter (fun i => α i = χ), a i - ∑ j ∈ S'.filter (fun j => β j = χ), b j)
    (fun ψ hψ => by
      simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hψ
      refine ⟨hψ.2, ?_⟩
      rcases hψ.1 with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      exacts [hα i hi, hβ i hi])
    (fun p => by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [grp S a α T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inl ⟨i, hi, rfl⟩, h0⟩),
        grp S' b β T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨i, hi, rfl⟩, h0⟩),
        h, sub_self])
  obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hj' := Finset.mem_filter.1 hj
  have := key χ (by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨j, hj'.1, hj'.2⟩, hχ⟩)
  rw [Finset.sum_eq_zero (s := S.filter _) fun i hi => by
    by_contra e; exact hn i (Finset.mem_filter.1 hi).1 e (Finset.mem_filter.1 hi).2, zero_sub, neg_eq_zero] at this
  exact hb (by convert this)
end
