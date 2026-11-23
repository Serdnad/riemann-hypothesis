module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep
open GlobalTheory.LFun (KGL heckeVec)
open GlobalTheory.Cong (Apart)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open Formalism.UG (Tj Ov IsUnifV)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem hecke_eq_sum {G : Type} [Group G] (K : Subgroup G) (h : G → ℂ) (h01 : ∀ g, h g ≠ 0 → h g = 1)
    (hfin : {q : G ⧸ K | h q.out ≠ 0}.Finite) : ∃ R : Finset G,
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
        heckeVec ρ K h x = ∑ g ∈ R, ρ g x := by
  refine ⟨hfin.toFinset.image Quotient.out, ?_⟩
  intro V _ _ ρ x
  rw [Finset.sum_image (fun a _ b _ e => Quotient.out_injective e)]
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ hfin.toFinset := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ hfin.toFinset, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h01 _ ((Set.Finite.mem_toFinset hfin).1 hq), one_smul]

private theorem tj_one {L : Type} [Field L] {n : ℕ} {O : Subring L} {ϖ : L} {j : ℕ} (g : GL (Fin n) L)
    (hg : Tj ℂ n O ϖ j g ≠ 0) : Tj ℂ n O ϖ j g = 1 := by
  unfold Tj at hg ⊢
  exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero hg) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem sum_mem_forms (hC : LocComm) (hM : LocMem) {w : Plc E} (hw : IsSplitAt w) {h : GLw n w → ℂ}
    (hh : h ∈ Formalism.UG.Hecke ℂ (KGL w (n := n))) {R : Finset (GLw n w)}
    (hR : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (v : V),
      heckeVec ρ (KGL w (n := n)) h v = ∑ g ∈ R, ρ g v)
    {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} (hS : w ∉ S) (hcS : cj w ∉ S)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ξ : Representation ℂ (Gam0 E n) V} {Φ : GUf E n → V}
    (hΦ : Φ ∈ forms rat (lev S Kw) ξ) :
    (fun g => ∑ y ∈ R, Φ (g * loc hw y)) ∈ forms rat (lev S Kw) ξ := by
  have hloc : ∀ y ∈ KGL w (n := n), loc hw y ∈ lev S Kw := fun y hy => (hM E n S Kw w hw hcS y).2 hS hy
  let ρ : Representation ℂ (GLw n w) (GUf E n → V) := (rightReg ℂ (GUf E n) V).comp (loc hw)
  have hρ : ∀ y (f : GUf E n → V) g, ρ y f g = f (g * loc hw y) := fun _ _ _ => rfl
  have hfix : Φ ∈ fixed ρ (KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    funext g
    rw [hρ]
    exact hΦ.2 _ (hloc k hk) g
  have hΨ := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed (Formalism.UG.Final.GLintComm E w n) hh hfix
  rw [hR] at hΨ
  have hΨ' := GlobalTheory.LGrp.mem_fixed.1 hΨ
  have hev : ∀ g, (∑ y ∈ R, ρ y Φ) g = ∑ y ∈ R, Φ (g * loc hw y) := fun g => by
    rw [Finset.sum_apply]
    rfl
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩

  · simp only [map_sum, mul_assoc]
    exact Finset.sum_congr rfl fun y _ => hΦ.1 γ _
  · have hx : comp w k ∈ KGL w (n := n) := (mem_lev.1 hk).2.2 w hS hcS
    set x := comp w k with hxdef
    set k' := (loc hw x)⁻¹ * k with hk'def
    have hk'm : k' ∈ lev S Kw := (lev S Kw).mul_mem ((lev S Kw).inv_mem (hloc x hx)) hk
    have hk'1 : comp w k' = 1 := by
      rw [hk'def, map_mul, map_inv, comp_loc, ← hxdef, inv_mul_cancel]
    have hcomm := (hC E n w hw).1 k' hk'1
    have hkk : k = loc hw x * k' := by rw [hk'def, mul_inv_cancel_left]
    have e1 : ∀ y, Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y) := fun y => by
      calc Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y * k') := by
            rw [hkk, mul_assoc g, mul_assoc _ k', hcomm y]; simp only [mul_assoc]
        _ = _ := hΦ.2 _ hk'm _
    have e2 := congrFun (hΨ' x hx) g
    rw [hρ, hev, hev] at e2
    show ∑ y ∈ R, Φ (g * k * loc hw y) = ∑ y ∈ R, Φ (g * loc hw y)
    rw [← e2]
    exact Finset.sum_congr rfl fun y _ => e1 y

theorem pHeckePres_of (hC : LocComm) (hM : LocMem) : HeckePres := by
  intro E _ _ _ n w hw ϖ hϖ i
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ i
  obtain ⟨R, hR⟩ := hecke_eq_sum (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ i) (fun g hg => tj_one g hg)
    (Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) hh.2)
  exact ⟨R, hR, fun S Kw hS hcS V _ _ ξ Φ hΦ => sum_mem_forms hC hM hw hh hR hS hcS hΦ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLevCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.LevCompact := by
  intro hC hI hL hO E _ _ _ n Up w₀ hw₀ S Kw hS
  obtain ⟨-, hAp, -, -, -, -⟩ := hL E n w₀ hw₀
  have hclosed : IsClosed (lev S Kw : Set (GUf E n)) :=
    Subgroup.isClosed_of_isOpen _ (hO E n S Kw hS.opn)
  have hK₁ := hC E n
  have hJ := hS.cpt w₀ hS.mem
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w₀ n).1
  obtain ⟨F, -, hF⟩ := hJ.elim_nhds_subcover
    (fun a => {y : GLw n w₀ | a⁻¹ * y ∈ GlobalTheory.LFun.KGL w₀ (n := n)}) (fun a _ => by
      refine IsOpen.mem_nhds (hKo.preimage (continuous_const.mul continuous_id)) ?_
      simp [Subgroup.one_mem])
  have hcov : IsCompact (⋃ a ∈ F, (fun x : GUf E n => loc hw₀ a * x) ''
      (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n))) :=
    F.isCompact_biUnion fun a _ => hK₁.image (continuous_const.mul continuous_id)
  refine hcov.of_isClosed_subset hclosed fun k hk => ?_
  obtain ⟨hsim, hmem, hoff⟩ := mem_lev.1 hk
  obtain ⟨a, haF, ha⟩ := Set.mem_iUnion₂.1 (hF (hmem w₀ hS.mem))
  have ha' : a⁻¹ * comp w₀ k ∈ GlobalTheory.LFun.KGL w₀ (n := n) := ha
  have hsim' : sim ((loc hw₀ a)⁻¹ * k) ∈ ZU := by simpa using hsim
  have hw : comp w₀ ((loc hw₀ a)⁻¹ * k) ∈ GlobalTheory.LFun.KGL w₀ (n := n) := by simpa using ha'
  have hint : ∀ u : Plc E, u ≠ w₀ → u ≠ cj w₀ → comp u k ∈ GlobalTheory.LFun.KGL u (n := n) := by
    intro u h1 h2
    have hcc : cj (cj u) = u := GlobalTheory.SplitPts.conjSrc_conjSrc_cm u
    by_cases hu : u ∈ S
    · exact hS.le u hu h1 (hmem u hu)
    by_cases hc : cj u ∈ S
    · have hne : cj u ≠ w₀ := fun h => h2 (by rw [← h, hcc])
      have := hI E n k (cj u) hsim (hS.le _ hc hne (hmem _ hc))
      rwa [hcc] at this
    · exact hoff u hu hc
  have hk' : (loc hw₀ a)⁻¹ * k ∈ lev (E := E) (n := n) ∅ (fun _ => ⊤) := by
    refine mem_lev.2 ⟨hsim', by simp, fun u _ _ => ?_⟩
    by_cases h1 : u = w₀
    · subst h1; exact hw
    by_cases h2 : u = cj w₀
    · subst h2; exact hI E n _ w₀ hsim' hw
    · have happ : GlobalTheory.Cong.Apart u w₀ := (hAp u).2 ⟨h1, h2⟩
      have : comp u ((loc hw₀ a)⁻¹ * k) = comp u k := by
        rw [map_mul, map_inv, comp_loc_of_apart hw₀ happ, inv_one, one_mul]
      rw [this]
      exact hint u h1 h2
  exact Set.mem_iUnion₂.2 ⟨a, haF, _, hk', by simp⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pFinToHecke_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke := by
  intro E _ _ ψ m ho hk
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E m
  let p : Neutral.B1.Ideles E →* (Af E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) : _ →* _)
  have hpc : Continuous p := Continuous.units_map _ continuous_snd
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ ho
  have hd : ∀ k : Eˣ, p (Neutral.B1.diagUnits E k) = diagF E k := fun k => Units.ext rfl
  have hl : ∀ (w : Plc E) y, p (Neutral.B1.localIdele E w y) = sgl w y := fun w y => Units.ext rfl
  have hi : ∀ k : Eˣ, p (infDiag k) = 1 := fun k => by
    rw [infDiag_eq]
    exact Units.ext rfl
  let θ : Neutral.B1.Ideles E →* ℂˣ := ψ.comp p * f
  have hθ : ∀ x, ((θ x : ℂˣ) : ℂ) = ((ψ (p x) : ℂˣ) : ℂ) * infPow m x := fun x => by
    rw [← hfe]
    rfl
  refine ⟨⟨θ, (hψ.comp hpc).mul hf, fun k => Units.ext ?_⟩, fun k _ => ?_, fun w y => ?_⟩
  · rw [hθ, hd, hk, infPow_diagUnits, Units.val_one]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))
  · show ((θ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hθ, hi, infPow_infDiag, infPow_diagUnits, map_one, Units.val_one, one_mul]
  · show θ (Neutral.B1.localIdele E w y) = _
    refine Units.ext ?_
    rw [hθ, hl, infPow_localIdele, mul_one]
end
