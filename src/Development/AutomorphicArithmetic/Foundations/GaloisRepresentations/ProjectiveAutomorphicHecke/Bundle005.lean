module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle786
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rop_single {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (u : H) (Φ : H → V) (g : H) :
    rop (Finsupp.single u 1) Φ g = Φ (g * u) := by
  unfold rop
  rw [Finsupp.sum_single_index (by simp), one_smul]

private theorem rop_sum {H V Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] (R : Finset Y) (e : Y → H) (Φ : H → V) (g : H) :
    rop (∑ y ∈ R, Finsupp.single (e y) 1) Φ g = ∑ y ∈ R, Φ (g * e y) := by
  unfold rop
  rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun y _ => by rw [Finsupp.sum_single_index (by simp), one_smul]

private structure HI {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (U : Submodule ℂ (UA E n → ℂ)) (S : Finset (Plc E)) where
  w : Plc E
  hw : IsSplitAt w
  h1 : w ∉ S
  h2 : cj w ∉ S
  B : Multiset ℂˣ
  hB : SatU U w B
  p : w.adicCompletion E
  hp : Formalism.UG.IsUnifV E w p
  i : ℕ
  hi : i ≤ n


theorem pFormGU_of (hExt : ExtEig2) (hCl : ClassFin) (hXi : XiZeta) (hKer : KerFormU) (hHk : HeckePres) (hSat : SatVal)
    (hMem : LocMem) (hComm : LocComm) (hOp : LevOpen) (hU : OfUBij) : FormGU := by
  intro E _ _ _ n x ζ hζ π W j Up w₀ hw₀ S Kw hS χ hχ f hf hf0 hfix
  obtain ⟨-, hap, -, -, hcc, -⟩ := hComm E n w₀ hw₀
  have hc0 : cj w₀ ∉ S := (hS.up w₀ hS.mem hw₀).2
  let Kw' := Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)
  have mem' : ∀ k : GUf E n, k ∈ lev S Kw' ↔ k ∈ lev S Kw ∧ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
    intro k
    have e0 : comp w₀ k ∈ Kw' w₀ ↔ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
      simp only [Kw', Function.update_self, Subgroup.mem_map, MonoidHom.mem_ker]
      exact ⟨fun ⟨y, hy, e⟩ => ⟨e ▸ y.2, by rw [← hy]; congr 1; exact Subtype.ext e.symm⟩, fun ⟨h, e⟩ => ⟨⟨_, h⟩, e, rfl⟩⟩
    have e1 : ∀ w, w ≠ w₀ → Kw' w = Kw w := fun w hw => Function.update_of_ne hw _ _
    rw [mem_lev, mem_lev]
    constructor
    · rintro ⟨a, b, c⟩
      obtain ⟨h, hh⟩ := e0.1 (b _ hS.mem)
      refine ⟨⟨a, fun w hw => ?_, c⟩, h, hh⟩
      by_cases e : w = w₀
      · subst e; exact h
      · rw [← e1 w e]; exact b w hw
    · rintro ⟨⟨a, b, c⟩, h⟩
      refine ⟨a, fun w hw => ?_, c⟩
      by_cases e : w = w₀
      · subst e; exact e0.2 h
      · rw [e1 w e]; exact b w hw
  have hopen : IsOpen (lev S Kw' : Set (GUf E n)) := by
    refine hOp E n S Kw' fun w hw => ?_
    by_cases e : w = w₀
    · subst e
      simp only [Kw', Function.update_self]
      exact (hS.opn w hw).isOpenMap_subtype_val _ hχ
    · simp only [Kw', Function.update_of_ne e]; exact hS.opn w hw
  have hfix' : ∀ u : finU (E := E) (n := n), ofU u ∈ lev S Kw' → algRep W u f = f := fun u hu => by
    obtain ⟨a, h, e⟩ := (mem' _).1 hu
    have := hfix u a h
    rwa [show χ ⟨cLoc w₀ u.1, h⟩ = 1 from e, Units.val_one, one_smul] at this
  obtain ⟨φ, hφ, hφu, hφ0⟩ := hKer E n W j f hf0 (lev S Kw') (fun k hk => (mem_lev.1 hk).1) hfix'
  have hloc : ∀ y : Kw w₀, loc hw₀ y.1 ∈ lev S Kw := fun y => (hMem E n S Kw w₀ hw₀ hc0 y.1).1 hS.mem y.2
  choose R hR1 hR2 using fun a : HI π.V S => hHk E n a.w a.hw a.p a.hp a.i
  have hsv : ∀ (w : Plc E) (hw : IsSplitAt w), w ∉ S → cj w ∉ S → ∀ B, SatU π.V w B →
      IsSatVecGL w ((algRep W).comp (locF hw)) f B := fun w hw h1 h2 B hB =>
    hSat E n π W f hf hf0 w hw (fun k hk => hfix' _ ((hMem E n S Kw' w hw h2 k).2 h1 hk)) B hB
  obtain ⟨Φ, hΦ, hΦ0, heig, ψ, hψ⟩ := hExt (Gam0 E n) (GUf E n) AfQˣ (Af E)ˣ _ rat (lev S Kw') (xi0 W j) sim ζ hζ.central
    (by
      obtain ⟨s, hs⟩ := hCl E ((lev S Kw').comap ζ) (hopen.preimage hζ.cont)
      refine ⟨s, fun z => ?_⟩
      obtain ⟨t, ht, o, ho, k, e⟩ := hs z
      obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
      exact ⟨t, ht, o, _, e, ho, γ, _, h1, h2⟩)
    φ hφ hφ0 (Kw w₀ ⊕ HI π.V S)
    (Sum.elim (fun y => Finsupp.single (loc hw₀ y.1) 1) fun a => ∑ y ∈ R a, Finsupp.single (loc a.hw y) 1)
    (Sum.elim (fun y => (χ y : ℂ)) fun a => satEig (Formalism.UG.qV E a.w) n a.B a.i)
    (by
      rintro (y | a) u hu
      · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hu)
        rfl
      · obtain ⟨y, -, hy⟩ := Finsupp.mem_support_finsetSum u hu
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hy)
        rfl)
    (by
      rintro (y | a) Ψ hΨ
      · refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
        · simp only [Sum.elim_inl, rop_single, mul_assoc, hΨ.1]
        · simp only [Sum.elim_inl, rop_single]
          obtain ⟨a, h, e⟩ := (mem' _).1 hk
          have hk' : (loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1 ∈ lev S Kw' := by
            have h' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) = (y⁻¹ * ⟨_, h⟩ * y : Kw w₀) := by
              rw [map_mul, map_mul, map_inv, comp_loc]; rfl
            have h'' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) ∈ Kw w₀ := by rw [h']; exact Subtype.property _
            refine (mem' _).2 ⟨mul_mem (mul_mem (inv_mem (hloc y)) a) (hloc y), h'', ?_⟩
            rw [show (⟨_, h''⟩ : Kw w₀) = y⁻¹ * ⟨_, h⟩ * y from Subtype.ext h', map_mul, map_mul, e, map_inv, mul_one,
              inv_mul_cancel]
          rw [← hΨ.2 _ hk' (g * loc hw₀ y.1)]
          simp only [mul_assoc, mul_inv_cancel_left]
      · have := hR2 a S Kw' a.h1 a.h2 _ (xi0 W j) Ψ hΨ
        convert this using 1
        funext g
        exact rop_sum _ _ _ _)
    (by
      rintro (y | a) g hg
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inl, rop_single]
        have h : cLoc w₀ (locF hw₀ y.1).1 ∈ Kw w₀ := by rw [cLoc_locF]; exact y.2
        have e := hfix (locF hw₀ y.1) (hloc y) h
        rw [show (⟨_, h⟩ : Kw w₀) = y from Subtype.ext (cLoc_locF _ _)] at e
        rw [show ofU u * loc hw₀ y.1 = ofU (u * locF hw₀ y.1) from (map_mul ofU _ _).symm, hφu, hφu]
        rw [Subgroup.coe_mul, ← algForms.val_algRep, e]
        rfl
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inr, rop_sum]
        have e := (hsv a.w a.hw a.h1 a.h2 a.B a.hB).2.2.2 a.p a.hp a.i a.hi
        rw [hR1 a] at e
        have e2 : ∀ y, φ (ofU u * loc a.hw y) = algForms.val (((algRep W).comp (locF a.hw)) y f) u.1 := fun y => by
          rw [show ofU u * loc a.hw y = ofU (u * locF a.hw y) from (map_mul ofU _ _).symm, hφu]
          rfl
        simp only [e2]
        let L : algForms W →ₗ[ℂ] Module.Dual ℂ W.Sp :=
          { toFun := fun F => algForms.val F u.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        have e3 := congrArg L e

        rw [map_sum, map_smul] at e3
        rw [hφu]
        exact e3)
  refine ⟨Φ, ψ, ⟨hΦ0, hΦ.1, fun k hk h g => ?_, fun w hw h1 h2 B hB => ⟨hΦ0, ?_, (hsv w hw h1 h2 B hB).2.2.1, fun p hp i hi => ?_⟩⟩, hψ.1⟩
  · have h1 := congrFun (heig (Sum.inl ⟨_, h⟩)) g
    simp only [Sum.elim_inl, rop_single, Pi.smul_apply] at h1
    have h' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) = 1 := by rw [map_mul, map_inv, comp_loc, inv_mul_cancel]
    have h'' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) ∈ Kw w₀ := by rw [h']; exact one_mem _
    have hk' : (loc hw₀ (comp w₀ k))⁻¹ * k ∈ lev S Kw' :=
      (mem' _).2 ⟨mul_mem (inv_mem (hloc ⟨_, h⟩)) hk, h'', by
        rw [show (⟨_, h''⟩ : Kw w₀) = 1 from Subtype.ext h', map_one]⟩
    rw [← h1, ← hΦ.2 _ hk' (g * loc hw₀ (comp w₀ k)), mul_assoc, mul_inv_cancel_left]
  · exact GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext fun g => hΦ.2 _ ((hMem E n S Kw' w hw h2 k).2 h1 hk) g
  · let a : HI π.V S := ⟨w, hw, h1, h2, B, hB, p, hp, i, hi⟩
    have h3 := heig (Sum.inr a)
    rw [show heckeVec _ _ _ Φ = _ from hR1 a _ _ Φ]
    refine Eq.trans ?_ h3
    funext g
    rw [Finset.sum_apply]
    exact (rop_sum _ _ _ _).symm

end UpperTheory.Gal.CertificateRingHomMap
end

section

open Module

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp only [rop, Pi.add_apply, smul_add, Finsupp.sum_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Pi.smul_apply, Finsupp.smul_sum, smul_smul, mul_comm]

private def eigForms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (r : J → H →₀ ℂ) (θ : J → ℂ) :
    Submodule ℂ (H → V) where
  carrier := {Φ | Φ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Φ = θ j • Φ}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun j => by rw [rop_add, ha', hb', smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun j => by
    have := rop_smul (r j) (0 : ℂ) (0 : H → V)
    simpa using this⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨Submodule.smul_mem _ a hb, fun j => by rw [rop_smul, hb', smul_comm]⟩

end

theorem pExtEig2_of : ExtZero → CentralEig2 → ExtEig2 := by
  intro hZ hC
  unfold ExtEig2
  intro Γ H A Z V _ _ _ _ _ _ ι K ξ c ζ hcen hs φ hφ hφne J r θ hsupp hforms heig
  obtain ⟨s, hs⟩ := hs
  obtain ⟨u₀, hu₀, hφu₀⟩ := hφne
  have memF : ∀ Ψ : H → V, Ψ ∈ forms ι K ξ ↔
      ((∀ γ g, Ψ (ι γ * g) = ξ γ (Ψ g)) ∧ ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) := fun Ψ => Iff.rfl
  obtain ⟨Φ, hΦ, hext, hsup⟩ := hZ Γ H A V ι K ξ c φ hφ
  obtain ⟨hΦ1, hΦ2⟩ := (memF Φ).1 hΦ
  have hΦne : Φ ≠ 0 := by
    intro h
    apply hφu₀
    rw [← hext u₀ hu₀, h]
    rfl
  have hΦeig : ∀ j, rop (r j) Φ = θ j • Φ := by
    intro j
    have hu : ∀ u, c u = 1 → rop (r j) Φ u = θ j • Φ u := by
      intro u hu
      rw [hext u hu, ← heig j u hu]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hext (u * v) (by rw [map_mul, hu, hsupp j v hv, one_mul])]
    obtain ⟨hf1, hf2⟩ := (memF _).1 (hforms j Φ hΦ)
    funext g
    by_cases hg : ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k
    · obtain ⟨γ, u, k, hu', hk, rfl⟩ := hg
      rw [Pi.smul_apply, mul_assoc, hf1 γ (u * k), hf2 k hk u, hΦ1 γ (u * k), hΦ2 k hk u,
        hu u hu', map_smul]
    · have h0 : Φ g = 0 := by
        by_contra h
        exact hg (hsup g h)
      rw [Pi.smul_apply, h0, smul_zero]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro v hv
      have hcv := hsupp j v hv
      have hz : Φ (g * v) = 0 := by
        by_contra h
        obtain ⟨γ, u, k, hu', hk, he⟩ := hsup _ h
        apply hg
        refine ⟨γ, u * (k * v⁻¹ * k⁻¹), k, ?_, hk, ?_⟩
        · simp [map_mul, map_inv, hu', hcv]
        · calc g = g * v * v⁻¹ := by group
            _ = ι γ * u * k * v⁻¹ := by rw [he]
            _ = ι γ * (u * (k * v⁻¹ * k⁻¹)) * k := by group
      rw [hz, smul_zero]
  have trForms : ∀ Ψ ∈ forms ι K ξ, ∀ z, (fun g => Ψ (g * ζ z)) ∈ forms ι K ξ := by
    intro Ψ hΨ z
    obtain ⟨h1, h2⟩ := (memF Ψ).1 hΨ
    refine (memF _).2 ⟨fun γ g => ?_, fun k hk g => ?_⟩
    · show Ψ (ι γ * g * ζ z) = ξ γ (Ψ (g * ζ z))
      rw [mul_assoc, h1]
    · show Ψ (g * k * ζ z) = Ψ (g * ζ z)
      rw [mul_assoc, ← hcen z k, ← mul_assoc, h2 k hk]
  have trRop : ∀ (Ψ : H → V) j z,
      rop (r j) (fun g => Ψ (g * ζ z)) = fun g => rop (r j) Ψ (g * ζ z) := by
    intro Ψ j z
    funext g
    simp only [rop, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [mul_assoc g (ζ z), hcen z u, mul_assoc]
  have key : ∀ z, ∃ t ∈ s, ∃ a : ℂ, (fun g => Φ (g * ζ z)) = a • fun g => Φ (g * ζ t) := by
    intro z
    obtain ⟨t, ht, z₀, z₁, rfl, hz₀, γ, a, hz₁, ha⟩ := hs z
    refine ⟨t, ht, a, ?_⟩
    funext g
    show Φ (g * ζ (t * z₀ * z₁)) = a • Φ (g * ζ t)
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← hcen z₁, hz₁, hΦ1, ha, hΦ2 _ hz₀]
  let M : Submodule ℂ (H → V) := Submodule.span ℂ ((fun t g => Φ (g * ζ t)) '' (s : Set Z))
  have hfin : FiniteDimensional ℂ M :=
    FiniteDimensional.span_of_finite ℂ ((s.finite_toSet).image _)
  have trM : ∀ z, (fun g => Φ (g * ζ z)) ∈ M := by
    intro z
    obtain ⟨t, ht, a, he⟩ := key z
    rw [he]
    exact M.smul_mem a (Submodule.subset_span ⟨t, ht, rfl⟩)
  have hΦM : Φ ∈ M := by
    have h := trM 1
    simp only [map_one, mul_one] at h
    exact h
  have hle : M ≤ eigForms ι K ξ r θ := by
    apply Submodule.span_le.2
    rintro _ ⟨t, _, rfl⟩
    show (fun g => Φ (g * ζ t)) ∈ forms ι K ξ ∧
      ∀ j, rop (r j) (fun g => Φ (g * ζ t)) = θ j • (fun g => Φ (g * ζ t))
    refine ⟨trForms Φ hΦ t, fun j => ?_⟩
    rw [trRop, hΦeig j]
    rfl
  have hE : ∀ Ψ ∈ M, Ψ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Ψ = θ j • Ψ := fun Ψ h => hle h
  have hne : M ≠ ⊥ := by
    intro h
    apply hΦne
    have h' := hΦM
    rw [h] at h'
    exact (Submodule.mem_bot ℂ).1 h'
  have hclos : ∀ Ψ ∈ M, ∀ z, (fun g => Ψ (g * ζ z)) ∈ M := by
    intro Ψ hΨ z
    have hL : M ≤ M.comap (LinearMap.funLeft ℂ V (fun g : H => g * ζ z)) := by
      apply Submodule.span_le.2
      rintro _ ⟨t, _, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := trM (z * t)
      simp only [map_mul, ← mul_assoc] at h
      exact h
    exact hL hΨ
  obtain ⟨Ψ, hΨM, hΨne, ψ, hψ⟩ :=
    hC Γ H Z V ι K ξ ζ hcen M hfin (fun Ψ h => (hE Ψ h).1) hne hclos
  exact ⟨Ψ, (hE Ψ hΨM).1, hΨne, (hE Ψ hΨM).2, ψ, hψ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem zpow_sum_eq_prod_zpow {ι : Type*} {a : ℂ} (ha : a ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ u ∈ s, e u) = ∏ u ∈ s, a ^ e u := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem UpperTheory.Gal.CertificateRingHomMap.pXiZeta_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar → UpperTheory.Gal.CertificateRingHomMap.XiZeta := by
  intro hXi E _ _ _ n W j x ζ hζ k
  obtain ⟨γ, t, h1, h2, h3, h4⟩ := hζ.onRat k
  refine ⟨γ, h1, fun v => ?_⟩
  have hs : xi0 W j γ v = _ := hXi E n W j γ.1.1 γ.1.2 t h2 v
  rw [hs]
  congr 1
  rw [h4]
  have e : ∀ u : InfinitePlace E, u.embedding (t : E) ^ (-∑ i, (W u).w i) =
      ∏ φ : E →+* ℂ, (if φ x = -u.embedding x then φ (k : E) else 1) ^ (-∑ i, (W u).w i) := by
    intro u
    rw [h3 u.embedding, Finset.prod_filter, Finset.prod_zpow]
  rw [Finset.prod_congr rfl fun u _ => e u, Finset.prod_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  have ha : φ (k : E) ≠ 0 := (map_ne_zero φ).2 k.ne_zero
  unfold mOf
  rw [zpow_sub₀ ha, div_eq_mul_inv, zpow_sum_eq_prod_zpow ha, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  by_cases h : φ x = -u.embedding x
  · have h' : u.embedding x = -φ x := by rw [h, neg_neg]
    rw [if_pos h, if_pos h', _root_.zpow_neg]
  · have h' : ¬ u.embedding x = -φ x := fun h'' => h (by rw [h'', neg_neg])
    rw [if_neg h, if_neg h']
    simp
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open scoped Pointwise

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem exists_cover_units (E : Type) [Field E] [NumberField E] (O : Subgroup (Af E)ˣ)
    (hO : IsOpen (O : Set (Af E)ˣ)) :
    ∃ F : Finset (Af E)ˣ, ∀ u ∈ GroundTheory.Global.finiteIntegralUnits E, ∃ f ∈ F, ∃ o ∈ O, u = f * o := by
  obtain ⟨t, ht⟩ := (GroundTheory.Global.isCompact_finiteIntegralUnits E).elim_finite_subcover
    (fun a : (Af E)ˣ => a • (O : Set (Af E)ˣ)) (fun a => hO.smul a)
    (fun c _ => Set.mem_iUnion.2 ⟨c, Set.mem_smul_set.2 ⟨1, one_mem O, mul_one c⟩⟩)
  refine ⟨t, fun u hu => ?_⟩
  obtain ⟨f, hf, huf⟩ := Set.mem_iUnion₂.1 (ht hu)
  obtain ⟨o, ho, rfl⟩ := Set.mem_smul_set.1 huf
  exact ⟨f, hf, o, ho, rfl⟩

private theorem mem_units_of_valued (E : Type) [Field E] [NumberField E] (u : (Af E)ˣ)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : Af E) P) = 1) :
    u ∈ GroundTheory.Global.finiteIntegralUnits E := by
  refine (GroundTheory.Global.mem_finiteIntegralUnits E).2 fun P => ⟨(hu P).le, ?_⟩
  have e : (((u⁻¹ : (Af E)ˣ) : Af E) P) * ((u : Af E) P) = 1 :=
    congrArg (fun t : Af E => t P) (Units.inv_mul u)
  have e2 := congrArg Valued.v e
  rw [map_mul, hu P, mul_one, map_one] at e2
  exact e2.le

theorem pClassFin_of : ClassFin := by
  intro E _ _ O hO
  classical
  obtain ⟨F, hF⟩ := exists_cover_units E O hO
  let ψ : (Af E)ˣ →* ClassGroup (𝓞 E) :=
    (ReciprocityTheory.Neutral.Bridge.HCFR.classOf E).comp GlobalTheory.ClassCover.toIdeles
  let sel : ClassGroup (𝓞 E) → (Af E)ˣ := fun c => if h : ∃ y, ψ y = c then h.choose else 1
  have hsel : ∀ y, ψ (sel (ψ y)) = ψ y := by
    intro y
    have h : ∃ z, ψ z = ψ y := ⟨y, rfl⟩
    simp only [sel, dif_pos h]
    exact h.choose_spec
  refine ⟨(Finset.univ.image sel ×ˢ F).image (fun p => p.1 * p.2), fun y => ?_⟩
  have hk : ψ ((sel (ψ y))⁻¹ * y) = 1 := by rw [map_mul, map_inv, hsel, inv_mul_cancel]
  obtain ⟨k, u, hu, he⟩ := GlobalTheory.ClassCover.eq_diag_mul_of_classOf _ hk
  obtain ⟨f, hf, o, ho, rfl⟩ := hF u (mem_units_of_valued E u hu)
  refine ⟨sel (ψ y) * f, Finset.mem_image.2 ⟨(sel (ψ y), f), Finset.mem_product.2
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hf⟩, rfl⟩, o, ho, k, ?_⟩
  have hy : y = sel (ψ y) * (diagF E k * (f * o)) := by
    rw [show diagF E k * (f * o) = (sel (ψ y))⁻¹ * y from he.symm, mul_inv_cancel_left]
  calc y = sel (ψ y) * (diagF E k * (f * o)) := hy
    _ = sel (ψ y) * f * o * diagF E k := by
      rw [mul_comm (diagF E k), ← mul_assoc, ← mul_assoc]

end UpperTheory.Gal.CertificateRingHomMap
end
