module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL)
open scoped Classical

private theorem scal_mem_KGL {E : Type} [Field E] [NumberField E] {n : ℕ} {u : Plc E}
    (a b : GL (Fin n) (u.adicCompletion E)) (t q : u.adicCompletion E)
    (ha : a.val = t • (1 : Matrix (Fin n) (Fin n) _)) (hb : b.val = q • (1 : Matrix (Fin n) (Fin n) _))
    (hq : q ≠ 0) (hv : Valued.v t = Valued.v q) : a⁻¹ * b ∈ KGL u (n := n) := by
  have hq' : Valued.v q ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have ht : t ≠ 0 := by
    rintro rfl
    exact hq' (by rw [← hv, map_zero])
  have hai : (a⁻¹).val = t⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; simp [smul_smul, ht])
  have hbi : (b⁻¹).val = q⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hb]; simp [smul_smul, hq])
  have e1 : (a⁻¹ * b).val = (t⁻¹ * q) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [Units.val_mul, hai, hb]; simp [smul_smul, mul_comm]
  have e2 : ((a⁻¹ * b)⁻¹).val = (q⁻¹ * t) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hbi, ha]; simp [smul_smul, mul_comm]
  have v1 : Valued.v (t⁻¹ * q) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have v2 : Valued.v (q⁻¹ * t) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have key : ∀ (c : u.adicCompletion E), Valued.v c = 1 → ∀ i j,
      Valued.v ((c • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E))) i j) ≤ 1 := by
    intro c hc i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [hc]
  refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]; exact key _ v1 i j
  · rw [e2]; exact key _ v2 i j

theorem UpperTheory.Gal.CertificateRingHomMap.pKapOf_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke → UpperTheory.Gal.CertificateRingHomMap.XiZeta → UpperTheory.Gal.CertificateRingHomMap.IntSim → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.KapOf := by
  intro hFH hXi hIS hLO E _ _ _ n hn x ζ hζ U W j Up w₀ S Kw hS χ hχ Φ ψ hΦ hψ
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, Φ g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ.ne (funext h)
  have cancel : ∀ a b : ℂ, a • Φ g₀ = b • Φ g₀ → a = b := fun a b h => smul_left_injective ℂ hg₀ h
  have A : ∀ k ∈ lev S Kw, ∀ h : comp w₀ k ∈ Kw w₀, χ ⟨comp w₀ k, h⟩ = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h h1 g
    rw [hΦ.right k hk h g, h1]
    simp
  have B : ∀ y, (∀ g, Φ (g * ζ y) = Φ g) → ψ y = 1 := by
    intro y hy
    have h := hy g₀
    rw [hψ] at h
    exact Units.ext (cancel _ 1 (by simpa using h))
  have C : ∀ k : GUf E n, (∀ u, comp u k ∈ KGL u (n := n)) → (∀ u ∈ S, comp u k = 1) → k ∈ lev S Kw :=
    fun k h1 h2 => mem_lev.2 ⟨hIS E n hn k h1, fun u hu => by rw [h2 u hu]; exact one_mem _, fun u _ _ => h1 u⟩
  have D : ∀ k ∈ lev S Kw, comp w₀ k = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h1 g
    have h : comp w₀ k ∈ Kw w₀ := by rw [h1]; exact one_mem _
    refine A k hk h ?_ g
    have e : (⟨comp w₀ k, h⟩ : Kw w₀) = 1 := Subtype.ext h1
    rw [e, map_one]

  have hKo : IsOpen ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) := by
    have e : ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) =
        Subtype.val '' {k : Kw w₀ | χ k = 1} := by
      ext a
      simp [Subgroup.mem_map, MonoidHom.mem_ker]
    rw [e]
    exact (hS.opn w₀ hS.mem).isOpenMap_subtype_val _ hχ
  have hK' := hLO E n S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)) (by
    intro w hw
    by_cases h : w = w₀
    · subst h
      simpa using hKo
    · simpa [Function.update_of_ne h] using hS.opn w hw)
  have hker : IsOpen (((ψ⁻¹).ker : Subgroup (Af E)ˣ) : Set (Af E)ˣ) := by
    refine Subgroup.isOpen_mono (H₁ := (lev S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype))).comap ζ) ?_
      (hK'.preimage hζ.cont)
    intro y hy
    have hy' := mem_lev.1 (Subgroup.mem_comap.1 hy)
    have h0 := hy'.2.1 w₀ hS.mem
    rw [Function.update_self] at h0
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 h0
    have hl : ζ y ∈ lev S Kw := by
      refine mem_lev.2 ⟨hy'.1, fun u hu => ?_, hy'.2.2⟩
      by_cases h : u = w₀
      · subst h
        rw [← hae]
        exact a.2
      · have := hy'.2.1 u hu
        rwa [Function.update_of_ne h] at this
    have h1 : ψ y = 1 := by
      refine B y fun g => A _ hl (by rw [← hae]; exact a.2) ?_ g
      have e : (⟨comp w₀ (ζ y), by rw [← hae]; exact a.2⟩ : Kw w₀) = a := Subtype.ext hae.symm
      rw [e]
      exact ha
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]
  have hprin : ∀ k : Eˣ, (((ψ⁻¹) (diagF E k) : ℂˣ) : ℂ) = (∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ)⁻¹ := by
    intro k
    obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
    have e : ((ψ (diagF E k) : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ := by
      apply cancel
      rw [← hψ, ← hζ.central, h1, hΦ.left, h2]
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e]
  obtain ⟨κ, halg, hloc⟩ := hFH E (ψ⁻¹) (mOf x W j) hker hprin
  refine ⟨κ, halg, ?_, ?_⟩
  · intro w hw y hy
    have h1 : ψ (sgl w y) = 1 := by
      refine B _ fun g => D _ (C _ (hζ.unit w y hy) fun u hu => hζ.off w y u (hw u hu)) ?_ g
      exact hζ.off w y w₀ (hw w₀ hS.mem)
    rw [hloc, MonoidHom.inv_apply, h1, inv_one]
  · intro w hw hnw z hz g
    have hv : κ.val w = (ψ (sgl w (atFin w (unif w))))⁻¹ := by
      show κ.loc w (atFin w (unif w)) = _
      rw [hloc, MonoidHom.inv_apply]
    have hq : ∀ u : Plc E, ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) ≠ 0 := by
      intro u
      have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      exact Nat.cast_ne_zero.2 h0
    have hc : ∀ u, comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) ∈ KGL u (n := n) ∧
        (¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1) := by
      intro u
      have hoff : ¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1 := by
        intro h
        rw [map_mul, map_inv, hζ.off w _ u h, (hz u).2 h, inv_one, one_mul]
      refine ⟨?_, hoff⟩
      by_cases h : SameK x (cj u) w
      · obtain ⟨t, ht, hvt⟩ := hζ.unif w _ (unif_spec w) hnw u h
        rw [map_mul, map_inv]
        exact scal_mem_KGL _ _ t _ ht ((hz u).1 h) (hq u) hvt
      · rw [hoff h]
        exact one_mem _
    have hk : (ζ (sgl w (atFin w (unif w))))⁻¹ * z ∈ lev S Kw :=
      C _ (fun u => (hc u).1) fun u hu => (hc u).2 (hw u hu)
    have e : z = ζ (sgl w (atFin w (unif w))) * ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) := by
      rw [mul_inv_cancel_left]
    rw [e, ← mul_assoc, D _ hk ((hc w₀).2 (hw w₀ hS.mem)), hψ, hv]
    simp
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhdU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private noncomputable def th {w : Plc E} (hw : IsSplitAt w) : GLw n w →* GLw n (cj w) :=
  (cLoc (cj w)).comp ((finU (E := E) (n := n)).subtype.comp (locF hw))

private theorem continuous_th {w : Plc E} (hw : IsSplitAt w) : Continuous (th (n := n) hw) :=
  (GlobalTheory.BCT.GlobLev.continuous_cLoc (cj w)).comp
    ((continuous_subtype_val (p := (· ∈ locU n w))).comp (locE hw).symm.continuous)

private theorem cLoc_cj_eq {w : Plc E} (hw : IsSplitAt w) (u : finU (E := E) (n := n)) :
    cLoc (cj w) u.1 = th hw (cLoc w u.1) :=
  GlobalTheory.LocInj.cLoc_conj_eq w u.1 (locF hw (cLoc w u.1)).1 (cLoc_locF hw _).symm

private theorem cj_cj (w : Plc E) : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w

private theorem exists_lt (α : Type) : ∃ lt : α → α → Prop, (∀ a b, a ≠ b → lt a b ∨ lt b a) ∧ ∀ a b, lt a b → ¬ lt b a := by
  refine ⟨WellOrderingRel, ?_, fun _ _ h => asymm h⟩
  intro a b h
  rcases trichotomous_of (WellOrderingRel : α → α → Prop) a b with hab | heq | hba
  · exact Or.inl hab
  · exact (h heq).elim
  · exact Or.inr hba

private def Top (lt : Plc E → Plc E → Prop) (Up : Plc E → Prop) (w₀ w : Plc E) : Prop :=
  Up w ∧ (Up (cj w) → w = w₀ ∨ (cj w ≠ w₀ ∧ lt w (cj w)))

private theorem top_or {lt : Plc E → Plc E → Prop} (h1 : ∀ a b, a ≠ b → lt a b ∨ lt b a) {Up : Plc E → Prop} (w₀ : Plc E)
    {w : Plc E} (hne : cj w ≠ w) (hup : Up w ∨ Up (cj w)) : Top lt Up w₀ w ∨ Top lt Up w₀ (cj w) := by
  by_cases ha : Up w
  · by_cases hb : Up (cj w)
    · by_cases e : w = w₀
      · exact Or.inl ⟨ha, fun _ => Or.inl e⟩
      · by_cases e' : cj w = w₀
        · exact Or.inr ⟨hb, fun _ => Or.inl e'⟩
        · rcases h1 w (cj w) hne.symm with h | h
          · exact Or.inl ⟨ha, fun _ => Or.inr ⟨e', h⟩⟩
          · exact Or.inr ⟨hb, fun _ => Or.inr ⟨by rwa [cj_cj], by rwa [cj_cj]⟩⟩
    · exact Or.inl ⟨ha, fun h => absurd h hb⟩
  · have hb := hup.resolve_left ha
    exact Or.inr ⟨hb, fun h => absurd (by rwa [cj_cj] at h) ha⟩

private theorem not_both {lt : Plc E → Plc E → Prop} (h2 : ∀ a b, lt a b → ¬ lt b a) {Up : Plc E → Prop} {w₀ w : Plc E}
    (hne : cj w ≠ w) (ha : Top lt Up w₀ w) (hb : Top lt Up w₀ (cj w)) : False := by
  have hb2 := hb.2 (by rw [cj_cj]; exact ha.1)
  rw [cj_cj] at hb2
  rcases ha.2 hb.1 with e | ⟨e, h⟩
  · rcases hb2 with e' | ⟨e', _⟩
    · exact hne (e'.trans e.symm)
    · exact e' e
  · rcases hb2 with e' | ⟨_, h'⟩
    · exact e e'
    · exact h2 _ _ h h'

end UpperTheory.Gal.CertificateRingHomMap.PNbhdU

open UpperTheory.Gal.CertificateRingHomMap.PNbhdU in
theorem UpperTheory.Gal.CertificateRingHomMap.pNbhdU_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.NbhdU := by
  intro h2 hI hL _ E _ _ _ n O hO Up hUp w₀ hw₀ hu₀
  obtain ⟨S₀, K₀, hK₀, hS₀⟩ := h2 E n O hO
  obtain ⟨lt, hlt1, hlt2⟩ := exists_lt (Plc E)
  have hne : ∀ w : Plc E, IsSplitAt w → cj w ≠ w := fun w hw => (hL E n w hw).2.2.1
  have hsp : ∀ w : Plc E, IsSplitAt w → IsSplitAt (cj w) := fun w hw => (hL E n w hw).2.2.2.1
  let T : Finset (Plc E) := insert w₀ (S₀ ∪ S₀.image (fun w => cj w))
  let S : Finset (Plc E) := T.filter (fun w => IsSplitAt w → Top lt Up w₀ w)
  let Kw : ∀ w : Plc E, Subgroup (GLw n w) := fun w =>
    if hw : IsSplitAt w then K₀ w ⊓ (K₀ (cj w)).comap (th hw) else K₀ w
  have hKle : ∀ w, Kw w ≤ K₀ w := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw]; exact inf_le_left
    · simp only [Kw, dif_neg hw]; exact le_rfl
  have hKopen : ∀ w, IsOpen (Kw w : Set (GLw n w)) := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw, Subgroup.coe_inf, Subgroup.coe_comap]
      exact (hK₀ w).1.inter ((hK₀ (cj w)).1.preimage (continuous_th hw))
    · simp only [Kw, dif_neg hw]; exact (hK₀ w).1
  have hKKGL : ∀ w, Kw w ≤ GlobalTheory.LFun.KGL w (n := n) := fun w => (hKle w).trans (hK₀ w).2
  have hmemS : ∀ w, w ∈ T → (IsSplitAt w → Top lt Up w₀ w) → w ∈ S := fun w h h' => Finset.mem_filter.2 ⟨h, h'⟩
  refine ⟨S, Kw, ⟨?_, fun w _ => hKopen w, fun w _ => ?_, fun w _ _ => hKKGL w, fun w hw hs => ?_⟩, ?_⟩
  · exact hmemS _ (Finset.mem_insert_self _ _) fun _ => ⟨hu₀, fun _ => Or.inl rfl⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Kw w) (hKopen w)) (hKKGL w)
  · have hw' := (Finset.mem_filter.1 hw).2 hs
    exact ⟨hw'.1, fun hc => not_both hlt2 (hne w hs) hw' ((Finset.mem_filter.1 hc).2 (hsp w hs))⟩
  · intro u hu
    obtain ⟨hz, hS, hout⟩ := mem_lev.1 hu
    have hint : ∀ w, cLoc w u.1 ∈ GlobalTheory.LFun.KGL w (n := n) := by
      intro w
      by_cases h1 : w ∈ S
      · exact hKKGL w (hS w h1)
      · by_cases h2 : cj w ∈ S
        · have h3 := hI E n (ofU u) (cj w) hz (hKKGL _ (hS _ h2))
          have key : ∀ v : Plc E, v = w → comp v (ofU u) ∈ GlobalTheory.LFun.KGL v (n := n) → cLoc w u.1 ∈ GlobalTheory.LFun.KGL w (n := n) := by
            rintro v rfl h; exact h
          exact key _ (cj_cj w) h3
        · exact hout w h1 h2
    refine hS₀ u hint fun w hw => ?_
    have hT : w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_left _ hw)
    by_cases hs : IsSplitAt w
    · by_cases ht : Top lt Up w₀ w
      · exact hKle w (hS w (hmemS w hT fun _ => ht))
      · have ht' := (top_or hlt1 w₀ (hne w hs) (hUp w hs)).resolve_left ht
        have hT' : cj w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))
        have h3 := hS (cj w) (hmemS _ hT' fun _ => ht')
        simp only [Kw, dif_pos (hsp w hs)] at h3
        have h4 : th (hsp w hs) (cLoc (cj w) u.1) ∈ K₀ (cj (cj w)) := (Subgroup.mem_inf.1 h3).2
        rw [← cLoc_cj_eq (hsp w hs) u] at h4
        have key : ∀ v : Plc E, v = w → cLoc v u.1 ∈ K₀ v → cLoc w u.1 ∈ K₀ w := by
          rintro v rfl h; exact h
        exact key _ (cj_cj w) h4
    · exact hKle w (hS w (hmemS w hT fun h => absurd h hs))
end
