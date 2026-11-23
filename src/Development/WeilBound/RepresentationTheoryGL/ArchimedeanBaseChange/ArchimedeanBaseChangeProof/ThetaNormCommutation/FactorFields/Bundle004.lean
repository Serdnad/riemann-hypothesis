module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
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
public import Mathlib.RingTheory.TensorProduct.Pi
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

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Invar2P

theorem index_ne_zero_of_open_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K U : Subgroup G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (R : Subgroup K)
    (hR : U.subgroupOf K ≤ R) : R.index ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K U hU)
  have h0 : (U.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h
  apply h0
  exact Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hR)

end PositivityTheory.Rg.BcB.G3.Invar2P

namespace PositivityTheory.Rg.BcB.G3

theorem invar2_pf : Invar2 := by
  intro E _ _ _ hU a b w K₁ K₂ hK₁ hK₂ φ hφ y g
  obtain ⟨-, -, -, -, hOa, hCa, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU a w
  obtain ⟨-, -, -, -, hOb, hCb, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU b w
  refine GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g φ fun x => ?_
  refine Invar2P.index_ne_zero_of_open_le ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) (K₁.prod K₂)
    (by rw [Subgroup.coe_prod]; exact hCa.prod hCb) (by rw [Subgroup.coe_prod]; exact hK₁.1.prod hK₂.1) _ ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  rw [GlobalTheory.TwOrbConj.mem_rStab]
  intro u
  have hθk : ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) ∈ K₁.prod K₂ :=
    Subgroup.mem_prod.2 ⟨hK₁.2.2 _ (Subgroup.mem_prod.1 hk).1, hK₂.2.2 _ (Subgroup.mem_prod.1 hk).2⟩
  have e : ((x * ((u * k : _) : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * ((u * k : _) : GLw a w × GLw b w))) =
      (k : GLw a w × GLw b w)⁻¹ * ((x * (u : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * (u : GLw a w × GLw b w))) *
        ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) := by
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]; group
  show φ _ = φ _
  rw [e, (hφ.2 _ hθk _).2, (hφ.2 _ ((K₁.prod K₂).inv_mem hk) _).1]

end PositivityTheory.Rg.BcB.G3
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinPol2P

theorem isLevel_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl, fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩

end PositivityTheory.Rg.BcB.G3.FinPol2P

open PositivityTheory.Rg.BcB.G3.FinPol2P in
theorem PositivityTheory.Rg.BcB.G3.finPol2_pf : FinPol2 := by
  intro E _ _ _ hU a b S hS φ hφc hφ1
  have hC₁ : ∀ w, IsCompact (Prod.fst '' tsupport (φ w)) := fun w => (hφc w).image continuous_fst
  have hC₂ : ∀ w, IsCompact (Prod.snd '' tsupport (φ w)) := fun w => (hφc w).image continuous_snd
  choose γ₁ hγ₁0 hγ₁ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E a w _ (hC₁ w)
  choose γ₂ hγ₂0 hγ₂ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E b w _ (hC₂ w)
  let good : Pl E → Prop := fun w => φ w = (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) :
    Set (GLw a w × GLw b w)).indicator 1
  let g₁ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₁ w
  let g₂ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₂ w
  have hfin₁ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E a S hS g₁
    (fun w => by by_cases h : good w <;> simp [g₁, h, hγ₁0]) (hφ1.mono fun w h => by simp [g₁, good, h])
  have hfin₂ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E b S hS g₂
    (fun w => by by_cases h : good w <;> simp [g₂, h, hγ₂0]) (hφ1.mono fun w h => by simp [g₂, good, h])
  refine (hfin₁.prod hfin₂).subset ?_
  rintro p ⟨h₁, h₂, hp⟩
  have key : ∀ w ∈ S, ((∀ i, Valued.v ((atPl w p.1).coeff i) ≤ g₁ w) ∧ (g₁ w)⁻¹ ≤ Valued.v ((atPl w p.1).coeff 0)) ∧
      ((∀ i, Valued.v ((atPl w p.2).coeff i) ≤ g₂ w) ∧ (g₂ w)⁻¹ ≤ Valued.v ((atPl w p.2).coeff 0)) := by
    intro w hw
    obtain ⟨y, hy, e₁, e₂⟩ := hp w hw
    rw [← e₁, ← e₂]
    by_cases hg : good w
    · simp only [g₁, g₂, if_pos hg, inv_one]
      have hy' : y ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) := by
        have hy2 := hy
        rw [show φ w = _ from hg] at hy2
        by_contra hc
        exact hy2 (Set.indicator_of_notMem hc _)
      exact ⟨GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E a w (isLevel_KGL hU a w) y.1 hy'.1,
        GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E b w (isLevel_KGL hU b w) y.2 hy'.2⟩
    · simp only [g₁, g₂, if_neg hg]
      have hyt : y ∈ tsupport (φ w) := subset_tsupport _ hy
      exact ⟨hγ₁ w y.1 ⟨y, hyt, rfl⟩, hγ₂ w y.2 ⟨y, hyt, rfl⟩⟩
  exact ⟨⟨h₁, fun w hw => (key w hw).1⟩, ⟨h₂, fun w hw => (key w hw).2⟩⟩

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.LocDictP

theorem frame_transport {k : Type} [Field k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B B' : Type}
    [CommRing B] [CommRing B'] {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (e : B ≃+* B')
    (h : IsFrame c δ s d ρ) : IsFrame c δ s (e d) (ρ.comp e.symm.toRingHom) := by
  refine ⟨h.inj.comp e.symm.injective, ?_, ?_, ?_, ?_⟩
  · simpa using h.sq
  · exact fun a => h.adj (e.symm a)
  · exact fun a => h.comm (e.symm a)
  · intro x hx
    obtain ⟨a, b, hab⟩ := h.span x hx
    exact ⟨e a, e b, by simpa using hab⟩

theorem decomp (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E) (hs0 : s ≠ 0)
    (hsc : IsCMField.complexConj E s = -s) (z : E) :
    ∃ a b : (maximalRealSubfield E),
      z = algebraMap (maximalRealSubfield E) E a + s * algebraMap (maximalRealSubfield E) E b := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (z + IsCMField.complexConj E z) / 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat,
      add_comm]
  have hb : (z - IsCMField.complexConj E z) / (2 * s) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat,
      hsc]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change z = (z + IsCMField.complexConj E z) / 2 + s * ((z - IsCMField.complexConj E z) / (2 * s))
  field_simp
  ring

end PositivityTheory.Rg.BcB.G3.LocDictP

open PositivityTheory.Rg.BcB.G3.LocDictP in
theorem PositivityTheory.Rg.BcB.G3.locDict_pf (h1 : ClsNorm) (h2 : ClsOnto) (h3 : ClsEq) (h4 : BaseFrame) (h5 : InertBase)
    (h6 : SplitSq) (h7 : TensorCompl) : LocDict := by
  intro E _ _ _ hU s d hs0 hsc hd n δ hsep ι _ K _ _ _ ρ hfr w y hy
  have hdne : d ≠ 0 := by
    rintro rfl
    apply hs0
    have : s ^ 2 = 0 := by rw [← hd, map_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  by_cases hw : IsSplitAt w
  ·
    have hthL : thL n w = MonoidHom.id _ := by simp only [thL, if_pos hw]
    have hy' : y.val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
      have := hy; simp only [nrmL, if_pos hw] at this; exact this
    refine ⟨fun _ _ => 1, fun t => ⟨fun _ => ?_, fun _ => ?_⟩⟩
    · intro i u
      obtain ⟨r, hr⟩ := h6 E s d hs0 hsc hd w hw
      obtain ⟨e, he⟩ := h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
      have hq : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u =
          algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := by
        rw [← he, ← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, ← hr, mul_one,
          Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      have hti : ((t : ∀ i, K i) i) ≠ 0 := ((t.isUnit.map (Pi.evalRingHom K i)).ne_zero)
      have hT : algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ i, K i) i) ≠ 0 := (_root_.map_ne_zero _).2 hti
      have hD : algebraMap (K i) (u.1.adicCompletion (K i)) (algebraMap (maximalRealSubfield E) (K i) d) ≠ 0 :=
        (_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hdne)
      have hq0 : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hq; exact hD hq.symm
      refine ⟨(1 + (algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹) / 2,
        ((algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹ - 1) / (2 * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u), ?_⟩
      have : CharZero (u.1.adicCompletion (K i)) :=
        charZero_of_injective_algebraMap (algebraMap (K i) (u.1.adicCompletion (K i))).injective
      simp only [Units.val_one]
      rw [← hq]
      field_simp
      ring
    · have hinv : ∀ x : E, (IsCMField.complexConj E).toRingEquiv.toRingHom
          ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = x := fun x => IsCMField.complexConj_apply_apply E x
      have hN := h1 E n _ hinv δ s hs0 hsc (∀ i, K i) _ ρ.toRingHom hfr t
      have hloc : locEl n w (pt δ ρ.toRingHom t) =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
        simp only [locEl, if_pos hw, thE, hN]
      have hc1 : y.val.charpoly = (locEl n w (pt δ ρ.toRingHom t)).val.charpoly := by
        rw [hloc, hy']
        change _ = (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly
        rw [Matrix.charpoly_map]
      obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable _ n y _ hc1 (hy' ▸ hsep.map)
      exact ⟨h, by rw [hthL, MonoidHom.id_apply]; exact hh⟩
  ·
    have hI := GlobalTheory.ConjAtPlace.main E hU w
    have hcc : ∀ x, cj w (cj w x) = x := hI.2.1
    have hcE := (hI.2.2.2.1 hw).1
    have : CharZero (w.adicCompletion E) :=
      charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
    obtain ⟨j, hj1, hj2, hj3⟩ := h5 E hU s d hs0 hsc hd w hw
    obtain ⟨ρ', hρ'1, hρ'⟩ := h4 (maximalRealSubfield E) E
      ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) (w.adicCompletion E)
      (algebraMap E _) j (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) s d hj1 (fun x => hcE x) hj2 hs0 hsc
      (decomp E s hs0 hsc) hj3 n δ hsep (∀ i, K i) ρ hfr
    have hTC := fun i => h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
    choose e he using hTC
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E]
        (∀ i, K i)) ≃+* (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)),
        ∀ a : (∀ i, K i), Φ (1 ⊗ₜ a) = fun i u => algebraMap (K i) _ (a i) :=
      ⟨(Algebra.TensorProduct.piRight (maximalRealSubfield E) (maximalRealSubfield E) _ K).toRingEquiv.trans
        (RingEquiv.piCongrRight e), fun a => by
          funext i u
          simp [Algebra.TensorProduct.piRight_tmul, he]⟩
    have hfr'' := frame_transport Φ hρ'
    have hmapθ := GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E))
      (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) (fun x => (hcE x).symm) δ
    have hNδ : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly =
        atPl w (δ * thE E n δ).val.charpoly := by
      rw [← hmapθ, ← map_mul]
      change (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly = _
      rw [Matrix.charpoly_map]
    have hsep' : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly.Separable := by
      rw [hNδ]; exact hsep.map
    have hy' : (y * thetaGL n (cj w) y).val.charpoly = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly := by
      rw [hNδ]
      have := hy; simp only [nrmL, if_neg hw] at this; exact this
    have hs0' : algebraMap E (w.adicCompletion E) s ≠ 0 := (_root_.map_ne_zero _).2 hs0
    have hsc' : cj w (algebraMap E (w.adicCompletion E) s) = -algebraMap E (w.adicCompletion E) s := by
      rw [hcE, hsc, map_neg]
    obtain ⟨t0, g0, hg0⟩ := h2 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' hsep' y hy'
    refine ⟨fun i u => Units.map (Pi.evalMonoidHom _ u) (Units.map (Pi.evalMonoidHom _ i) t0), fun t => ?_⟩
    obtain ⟨T, hT⟩ : ∃ T : (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i))ˣ,
        (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) = Φ (1 ⊗ₜ (t : ∀ i, K i)) :=
      ⟨Units.map (Φ.toMonoidHom.comp
        (Algebra.TensorProduct.includeRight : (∀ i, K i) →ₐ[maximalRealSubfield E] _).toRingHom.toMonoidHom) t, rfl⟩
    have hpt : locEl n w (pt δ ρ.toRingHom t) = pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
        (ρ'.comp Φ.symm.toRingHom) T := by
      apply Units.ext
      simp only [locEl, if_neg hw, pt]
      change ((ρ t * δ.val).map (algebraMap E (w.adicCompletion E))) =
        ρ' (Φ.symm (T : _)) * (δ.val.map (algebraMap E (w.adicCompletion E)))
      rw [hT, RingEquiv.symm_apply_apply, hρ'1, Matrix.map_mul]
    have hthL : thL n w = thetaGL n (cj w) := by simp only [thL, if_neg hw]
    rw [hpt, hthL]
    have step1 : (∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) (ρ'.comp Φ.symm.toRingHom) T =
        g⁻¹ * y * thetaGL n (cj w) g) ↔ ∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
          (ρ'.comp Φ.symm.toRingHom) T = g⁻¹ * pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
            (ρ'.comp Φ.symm.toRingHom) t0 * thetaGL n (cj w) g := by
      rw [hg0]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g0 * g, by rw [hg, map_mul]; group⟩
      · rintro ⟨g, hg⟩
        exact ⟨g0⁻¹ * g, by rw [hg, map_mul, map_inv]; group⟩
    rw [step1, h3 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' t0 T]
    have hTv : ∀ i u, (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) i u =
        algebraMap (K i) _ ((t : ∀ i, K i) i) := fun i u => by rw [hT, hΦ]
    have hdv : ∀ i u, Φ (1 ⊗ₜ algebraMap (maximalRealSubfield E) (∀ i, K i) d) i u =
        algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := fun i u => by rw [hΦ]; rfl
    constructor
    · rintro ⟨U, V, hUV⟩ i u
      refine ⟨U i u, V i u, ?_⟩
      have := congrFun (congrFun hUV i) u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv] at this
      simpa using this
    · intro h
      choose a b hab using h
      refine ⟨fun i u => a i u, fun i u => b i u, ?_⟩
      funext i u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv]
      simpa using hab i u
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinCl2P

theorem rel_of_eqvGen {G : Type} [Group G] (θ : G →* G) {x y : G}
    (h : Relation.EqvGen (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x y) : ∃ g, y = g⁻¹ * x * θ g := by
  induction h with
  | rel a b hab => exact hab
  | refl a => exact ⟨1, by simp⟩
  | symm a b _ ih =>
    obtain ⟨g, rfl⟩ := ih
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  | trans a b c _ _ ih1 ih2 =>
    obtain ⟨g, rfl⟩ := ih1
    obtain ⟨k, rfl⟩ := ih2
    exact ⟨g * k, by rw [map_mul]; group⟩

theorem twConj_of_mk_eq {G : Type} [Group G] {θ : G →* G} {x y : G}
    (h : (Quot.mk _ x : TwCl θ) = Quot.mk _ y) : ∃ g, y = g⁻¹ * x * θ g :=
  rel_of_eqvGen θ (Quot.eqvGen_exact h)

theorem rep_mk {G : Type} [Group G] {θ : G →* G} (y : G) :
    ∃ g, TwCl.rep (Quot.mk _ y : TwCl θ) = g⁻¹ * y * θ g :=
  twConj_of_mk_eq (θ := θ) (Quot.out_eq (Quot.mk _ y : TwCl θ)).symm

theorem charpoly_rep_mk {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : GLw n w) : (nrmL n w (TwCl.rep (Quot.mk _ y : TwCl (thL n w)))).val.charpoly = (nrmL n w y).val.charpoly := by
  obtain ⟨g, hg⟩ := rep_mk (θ := thL n w) y
  rw [hg, GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g y, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']

end PositivityTheory.Rg.BcB.G3.FinCl2P

open PositivityTheory.Rg.BcB.G3.FinCl2P in
theorem PositivityTheory.Rg.BcB.G3.finCl2_pf : FinCl2 := by
  intro E _ _ _ hU a b w Q₁ Q₂ h₁ h₂
  set θ := (thL a w).prodMap (thL b w) with hθ
  let f : TwCl θ → TwCl (thL a w) × TwCl (thL b w) := fun l => (Quot.mk _ l.rep.1, Quot.mk _ l.rep.2)
  have hinj : Function.Injective f := by
    intro l l' hll'
    obtain ⟨g₁, hg₁⟩ := twConj_of_mk_eq (congrArg Prod.fst hll')
    obtain ⟨g₂, hg₂⟩ := twConj_of_mk_eq (congrArg Prod.snd hll')
    have hq : (Quot.mk _ l.rep : TwCl θ) = Quot.mk _ l'.rep :=
      Quot.sound ⟨(g₁, g₂), Prod.ext (by simpa [hθ] using hg₁) (by simpa [hθ] using hg₂)⟩
    have e1 : (Quot.mk _ l.rep : TwCl θ) = l := Quot.out_eq l
    have e2 : (Quot.mk _ l'.rep : TwCl θ) = l' := Quot.out_eq l'
    rw [← e1, ← e2, hq]
  have hA := (GlobalTheory.BCT.ClsFin.classes_finite E hU a w Q₁ h₁).1
  have hB := (GlobalTheory.BCT.ClsFin.classes_finite E hU b w Q₂ h₂).1
  refine ((hA.prod hB).preimage hinj.injOn).subset ?_
  rintro l ⟨hl₁, hl₂⟩
  refine ⟨?_, ?_⟩
  · change (nrmL a w (TwCl.rep (Quot.mk _ l.rep.1 : TwCl (thL a w)))).val.charpoly = Q₁
    rw [charpoly_rep_mk hU a w, hl₁]
  · change (nrmL b w (TwCl.rep (Quot.mk _ l.rep.2 : TwCl (thL b w)))).val.charpoly = Q₂
    rw [charpoly_rep_mk hU b w, hl₂]
end
