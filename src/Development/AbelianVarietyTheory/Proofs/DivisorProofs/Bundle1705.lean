module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdThSympl

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

def perL (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun u := fun j => perC X x u (idx j)
  map_add' u v := by
    funext j
    simp only [perC, Pi.add_apply]
    split_ifs
    · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' c u := by
    funext j
    simp only [perC, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

variable {X} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)


include idx in
theorem span_emb (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range fun (v : Fin r → E) (τ : X.Ψ) => Data.emb τ.1 v) = ⊤ := by
  have h1 : (Submodule.span ℝ (Set.range fun (v : Fin r → E) (τ : X.Ψ) => Data.emb τ.1 v)).map (perL X idx x) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_range_pv idx hs hx
  have hsurj : Function.Surjective (perL X idx x) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← h1]
    exact LinearMap.map_le_range
  have hd : Module.finrank ℝ (X.Ψ → Fin r → ℂ) = Module.finrank ℝ (Fin g → ℂ) := by
    have := Fintype.card_congr idx
    simp only [Fintype.card_fin, Fintype.card_prod] at this
    simp only [Module.finrank_pi_fintype, finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, this]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hsurj
  apply Submodule.map_injective_of_injective hinj
  rw [h1, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]

theorem im_hx_perC (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : X.Ψ → Fin r → ℂ) :
    (GlobalTheory.Dict.hx X bas idx x (fun j => perC X x u (idx j)) (fun j => perC X x v (idx j))).im =
      ∑ τ : X.Ψ, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (u τ) (v τ)).re := by
  let B₁ : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => (Geo.Tor.hermForm (ThFr.Hm X bas idx x) (perL X idx x u) (perL X idx x v)).im)
    (fun u u' v => by simp only [Geo.Tor.hermForm, map_add (f := _), add_dotProduct, add_im])
    (fun c u v => by simp only [Geo.Tor.hermForm, map_smul, smul_dotProduct, smul_im])
    (fun u v v' => by simp only [Geo.Tor.hermForm, map_add (f := _), star_add, mulVec_add, dotProduct_add, add_im])
    (fun c u v => by simp only [Geo.Tor.hermForm, map_smul, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_im])
  let B₂ : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => ∑ τ : X.Ψ, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (u τ) (v τ)).re)
    (fun u u' v => by simp only [hermC, Pi.add_apply, add_mul, mul_add, add_re, Finset.sum_add_distrib])
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [mul_left_comm c, ← re_ofReal_mul c, mul_left_comm (c : ℂ)]
      congr 3
      simp only [hermC, Finset.mul_sum, Pi.smul_apply, real_smul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun u v v' => by simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, add_re, Finset.sum_add_distrib])
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [mul_left_comm c, ← re_ofReal_mul c, mul_left_comm (c : ℂ)]
      congr 3
      simp only [hermC, Finset.mul_sum, Pi.smul_apply, real_smul, map_mul, conj_ofReal]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have hB : B₁ = B₂ := by
    refine LinearMap.ext_on_range (span_emb idx hs hx) fun a => LinearMap.ext_on_range (span_emb idx hs hx) fun b => ?_
    have h1 : (Geo.Tor.hermForm (ThFr.Hm X bas idx x) (pv X idx x a) (pv X idx x b)).im = (EF X a b : ℝ) :=
      im_hermForm_Hm idx hs hx a b
    refine h1.trans ?_
    rw [EF_def, TraceFormIndependence.trace_re X]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : τ.1 (herm X.Gm a b) = hermC τ.1 X.Gm (Data.emb τ.1 a) (Data.emb τ.1 b) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [herm, hermC, map_sum, map_mul, Data.emb, cc, IsCMField.complexEmbedding_complexConj]
    rw [map_mul, h2]
  rw [hx_eq_hermForm]
  exact LinearMap.congr_fun₂ hB u v

end Classical

theorem realM_tauE {D : D7} (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dite_eq_left h, ← GlobalTheory.StdRat.tauE_injective D h.choose_spec]

theorem sum_four {m n : ℕ} (c : ℂ) (G : Fin m → Fin m → ℂ) (x y : Fin m → Fin n → ℂ) :
    ∑ b, 2 * (c * ∑ d, ∑ e, x d b * -G e d * conj (y e b)).re =
      -(2 * (c * ∑ a, ∑ b, ∑ e, ∑ d, (if a = b then (1 : ℂ) else 0) * conj (y e b) * G e d * x d a).re) := by
  rw [← Finset.mul_sum, ← re_sum, ← Finset.mul_sum, ← mul_neg, ← neg_re, ← mul_neg]
  congr 3
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb.symm]) (by simp), Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib, if_true]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem psi_symplOH_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV _ hM hs x hx v w hv
  subst hr
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (GlobalTheory.FockCompare.real_adele_ext_and_char D θ σ hσ _ (GlobalTheory.OrientedHeis.snd_symplO (y := w) (Or.inl hv))).2 ψ hψ
  rw [Finset.sum_congr rfl fun τ _ => GlobalTheory.OrientedHeis.valTau_symplO hθ τ v w] at e
  refine e.trans ?_
  congr 1
  rw [neg_mul, ← mul_neg, ← ofReal_neg]
  congr 2
  unfold zOf
  simp only [im_hx_perC idx hs hx]
  rw [Finset.sum_comm]
  have hb : Function.Bijective fun ρ : D.what₂.Tau => (⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩ : X.Ψ) :=
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hM.psi τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  rw [← hb.sum_comp]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hk : -(X.κ0 / 2) = D.host.xi0 := by rw [hM.kap]; ring
  have hG : ∀ a b, tauE D ρ (X.Gm a b) = -tauE D ρ (W.gram b a) := fun a b => by
    rw [hM.model.1, ← map_neg]; rfl
  have h1 : ∀ a b, tauE D ρ (V.gram⁻¹ a b) = if a = b then 1 else 0 := fun a b => by
    rw [hV, inv_one, Matrix.one_apply]; split_ifs <;> simp
  simp only [realM_tauE, hk, hermC, hG, GlobalTheory.OrientedHeis.formAt, h1]
  exact (sum_four _ (fun e d => tauE D ρ (W.gram e d)) _ _).symm

theorem psi_symplOH_eq_of_isONFr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) :=
  fun D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx =>
    psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x (PIW.FdPA.orthonormal_domain r X x hx)

end GlobalTheory.AdThSympl

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.HSupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_cLoc_val (hE : Unr E) (w : Pl E) (x : finU (E := E) (n := n)) :
    ((toSub (UL n w) (cLoc w (x : UA E n)) : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  unfold toSub
  rw [dite_eq_left (cLoc_mem_UL E hE n w x)]

theorem factor_ne_zero (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : ∀ᶠ w in cofinite, K' w = KL n w)
    (f : ∀ w : Pl E, UL n w → ℂ) (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (x : finU (E := E) (n := n)) (hx : globFn S f x ≠ 0) :
    ∀ w ∈ S, f w (toSub (UL n w) (cLoc w (x : UA E n))) ≠ 0 := by
  set g : Pl E → ℂ := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n))) with hg
  have hB : {w | ¬ (f w = (KL n w : Set (UL n w)).indicator 1 ∧
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w)}.Finite :=
    Filter.eventually_cofinite.1 (hf.and (RegVan.eventually_toSub_mem (n := n) x))
  have hfin : (S ∩ Function.mulSupport g).Finite := by
    refine hB.subset fun w hw => ?_
    intro hc
    apply hw.2
    change f w _ = 1
    rw [hc.1]
    exact Set.indicator_of_mem hc.2 _
  intro w hwS
  by_cases hm : w ∈ Function.mulSupport g
  · have hx' : ∏ᶠ w ∈ S, g w ≠ 0 := hx
    rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin] at hx'
    exact Finset.prod_ne_zero_iff.1 hx' w (hfin.mem_toFinset.2 ⟨hwS, hm⟩)
  · rw [Function.notMem_mulSupport] at hm
    change g w ≠ 0
    rw [hm]
    exact one_ne_zero

end GlobalTheory.BCT.HSupp


open GlobalTheory.BCT.HSupp in
theorem GlobalTheory.BCT.finite_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → {q : finU (E := E) (n := n) ⧸ globLev S K' | globFn S f q.out ≠ 0}.Finite := by
  intro E _ _ _ hE n S K' hK f hf
  set F : Set (Pl E) := {w | ¬ (K' w = KL n w ∧ f w = (KL n w : Set (UL n w)).indicator 1)} with hF
  have hFfin : F.Finite := Filter.eventually_cofinite.1 (hK.2.and hf.2)
  have key := factor_ne_zero S K' hK.2 f hf.2
  have inK : ∀ x : finU (E := E) (n := n), globFn S f x ≠ 0 → ∀ w ∈ S, w ∉ F →
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ K' w := by
    intro x hx w hwS hwF
    simp only [hF, Set.mem_setOf_eq, not_not] at hwF
    have h := key x hx w hwS
    rw [hwF.2] at h
    rw [hwF.1]
    by_contra hc
    exact h (Set.indicator_of_notMem hc _)
  haveI : Finite ↥(F ∩ S) := (hFfin.inter_of_left S).to_subtype
  let Φ : finU (E := E) (n := n) ⧸ globLev S K' → ∀ w : ↥(F ∩ S), UL n w.1 ⧸ K' w.1 := fun q w =>
    (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)) : UL n w.1 ⧸ K' w.1)
  refine Set.Finite.of_injOn (f := Φ)
    (t := Set.pi Set.univ fun w : ↥(F ∩ S) => {c : UL n w.1 ⧸ K' w.1 | f w.1 c.out ≠ 0}) ?_ ?_
    (Set.Finite.pi fun w => LevOpTmul.finite_supp (hK.1 w.1).1 (hf.1 w.1).1)
  · intro q hq w _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K' w.1) (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)))
    change f w.1 (QuotientGroup.mk _ : UL n w.1 ⧸ K' w.1).out ≠ 0
    rw [hh, ((hf.1 w.1).2 h h.2 _).2]
    exact key _ hq w.1 w.2.2
  · intro q₁ hq₁ q₂ hq₂ he
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    refine QuotientGroup.eq.2 ((mem_globLev_iff S K' _).2 fun w hwS => ?_)
    refine ⟨(toSub (UL n w) (cLoc w (q₁.out : UA E n)))⁻¹ * toSub (UL n w) (cLoc w (q₂.out : UA E n)), ?_, ?_⟩
    · by_cases hwF : w ∈ F
      · have := congrFun he ⟨w, hwF, hwS⟩
        exact QuotientGroup.eq.1 this
      · exact mul_mem (inv_mem (inK _ hq₁ w hwS hwF)) (inK _ hq₂ w hwS hwF)
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, toSub_cLoc_val hE, toSub_cLoc_val hE, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv]
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

theorem GlobalTheory.LeviDesc.hint_comp_linear : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  intro E _ _ w a b L φ hL hU hc
  obtain ⟨Λ, hΛo, hΛc, hΛ⟩ := GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup E w a b
  obtain ⟨hU', hc', hlc⟩ := GlobalTheory.T.comp_linearAut_locallyConstant_compactSupport_matrix E w a b L φ hL hU hc
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := ⟨rfl⟩
  let μ : Measure (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  rw [hΛ, GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU' hc', GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU hc,
    GlobalTheory.T.integral_comp_linearMap_matrix_nonarchLocalField _ a b L hL φ μ hμ, GlobalTheory.T.adicCompletion_distribHaarChar_eq_absHalf_sq E w _ hL]
  ring
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.pullback_real_polynomial_even_form_fields : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  first | exact @GlobalTheory.LineForm.pullback_evalF | exact GlobalTheory.LineForm.pullback_evalF | (intros; apply GlobalTheory.LineForm.pullback_evalF <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.separable_charpoly_of_testFunction_ne_zero_regularPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU (E := E) (n := n)) (γ : UE E n), globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable := by
  first | exact @GlobalTheory.BCT.regvan | exact GlobalTheory.BCT.regvan | (intros; apply GlobalTheory.BCT.regvan <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  first | exact @GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | exact GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | (intros; apply GlobalTheory.BCT.HintInv.hint_intMat_mul_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedConstantTermSplitPlace_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w →
    (∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a b w (ctMu h w μ f) := by
  first | exact @GlobalTheory.BCT.CtReg.ctMu_regAt2 | exact GlobalTheory.BCT.CtReg.ctMu_regAt2 | (intros; apply GlobalTheory.BCT.CtReg.ctMu_regAt2 <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  first | exact @GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | exact GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | (intros; apply GlobalTheory.BCT.SplitChar.locK_mul_locK_conj <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc.ConjStab

variable {E : Type} [Field E] [NumberField E]

def dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := blk h w k 0
  map_one' := by
    ext : 1
    rw [LeviBlockConjugation.blk_val]
    simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Matrix.reindex_apply]
    exact Matrix.submatrix_one_equiv _
  map_mul' k k' := by
    ext : 1
    simp only [Units.val_mul, LeviBlockConjugation.blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp

theorem continuous_dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : Continuous (dgHom (E := E) h w) := by
  rw [Units.continuous_iff]
  constructor
  · have e : (fun k : GLw a w × GLw b w => (dgHom h w k).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks k.1.val (k.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 k.2.val) := by
      funext k; exact LeviBlockConjugation.blk_val h w k 0
    change Continuous fun k : GLw a w × GLw b w => (dgHom h w k).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst)
      ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · have e : (fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks (k.1⁻¹).val ((k.1⁻¹).val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 (k.2⁻¹).val) := by
      funext k; rw [← map_inv]; exact LeviBlockConjugation.blk_val h w k⁻¹ 0
    change Continuous fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst)
      ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

def conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw a w × GLw b w →* GLw n w :=
  (MulAut.conj (blk h w 1 X)⁻¹).toMonoidHom.comp (dgHom h w)

theorem conjLevi_apply {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (k : GLw a w × GLw b w) : conjLevi h w X k = (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X := by
  simp [conjLevi, dgHom, MulAut.conj_apply]

theorem continuous_conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Continuous (conjLevi h w X) := by
  have e : (conjLevi h w X : GLw a w × GLw b w → GLw n w) = fun k => (blk h w 1 X)⁻¹ * dgHom h w k * blk h w 1 X := by
    funext k; rw [conjLevi_apply]; rfl
  rw [e]
  exact (continuous_const.mul (continuous_dgHom h w)).mul continuous_const

end GlobalTheory.LeviDesc.ConjStab


open GlobalTheory.LeviDesc.ConjStab in
theorem GlobalTheory.LeviDesc.ConjStab.exists_stab : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w),
    U ≤ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) ∧ U.relIndex ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ≠ 0 ∧
    ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ n a b h w X
  set P : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))
  set C : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w (n := n)).comap (conjLevi h w X)
  refine ⟨P ⊓ C, inf_le_left, ?_, fun k hk => ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    have hP : IsCompact (P : Set (GLw a w × GLw b w)) := by
      simp only [P, Subgroup.coe_prod]
      exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
    have hC : IsOpen (C : Set (GLw a w × GLw b w)) :=
      (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage (continuous_conjLevi h w X)
    haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    haveI : Finite (P ⧸ C.subgroupOf P) :=
      Subgroup.quotient_finite_of_isOpen _ (hC.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  · have := (Subgroup.mem_inf.1 hk).2
    rw [Subgroup.mem_comap, conjLevi_apply] at this
    exact this
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  first | exact @GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | exact GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | (intros; apply GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split <;> assumption)
end
