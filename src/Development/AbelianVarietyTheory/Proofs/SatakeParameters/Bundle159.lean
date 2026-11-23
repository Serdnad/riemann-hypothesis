module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

private theorem sorted_list_sign_split (d : List ℤ) (h : d.Pairwise (fun a b => b ≤ a)) :
    d = d.filter (fun x => decide (0 < x)) ++ d.filter (fun x => decide (x = 0)) ++ d.filter (fun x => decide (x < 0)) := by
  induction d with
  | nil => rfl
  | cons x t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hx, ht⟩ := h
    have ih := ih ht
    rcases lt_trichotomy 0 x with hpos | hzero | hneg
    · have h1 : ¬ x = 0 := by omega
      have h2 : ¬ x < 0 := by omega
      rw [List.filter_cons_of_pos (by simp [hpos]), List.filter_cons_of_neg (by simp [h1]),
        List.filter_cons_of_neg (by simp [h2]), List.cons_append, List.cons_append, ← ih]
    · subst hzero
      have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; simpa using hx y hy
      rw [e1, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp),
        List.filter_cons_of_neg (by simp), e1, List.nil_append, List.cons_append, ← ih]
    · have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have e2 : t.filter (fun x => decide (x = 0)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have h1 : ¬ 0 < x := by omega
      have h2 : ¬ x = 0 := by omega
      rw [e1, e2, List.nil_append, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_neg (by simp [h2]),
        List.filter_cons_of_pos (by simp [hneg]), e1, e2, List.nil_append, List.nil_append, ← ih]

private theorem flatMap_singleton_natCast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

private theorem label_list_eq_signed (n : ℕ) (s : List ℕ) : labIn n s =
    s.map (fun a : ℕ => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a : ℕ => -(a : ℤ)) := by
  unfold labIn
  show List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s) ++ _ ++
      List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s.reverse) = _
  rw [flatMap_singleton_natCast, flatMap_singleton_natCast]
  simp [List.map_map, Function.comp_def]

theorem labIn_selfDual_iff : ∀ (n : ℕ) (d : List ℤ), (d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d) ↔
    ∃ s : List ℕ, 2 * s.length ≤ n ∧ s.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ s, 0 < a) ∧ d = labIn n s := by
  intro n d
  constructor
  · rintro ⟨hlen, hsort, hdual⟩
    have hsplit := sorted_list_sign_split d hsort
    set P := d.filter (fun x => decide (0 < x)) with hPdef
    set Z := d.filter (fun x => decide (x = 0)) with hZdef
    set N := d.filter (fun x => decide (x < 0)) with hNdef
    have hPN : P = (N.map Neg.neg).reverse := by
      have e : P = (dualLab d).filter (fun x => decide (0 < x)) := by rw [hdual]
      rw [e, dualLab, List.filter_reverse, List.filter_map, hNdef]
      congr 2
      apply List.filter_congr
      intro x _
      simp
    have hN : N = P.reverse.map Neg.neg := by
      rw [hPN, List.reverse_reverse, List.map_map]
      simp
    have hZ : Z = List.replicate Z.length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨rfl, ?_⟩
      intro b hb
      rw [hZdef] at hb
      simpa using (List.mem_filter.mp hb).2
    have hlenPN : N.length = P.length := by rw [hN, List.length_map, List.length_reverse]
    have hdlen : d.length = P.length + Z.length + N.length := by
      have := congrArg List.length hsplit
      simpa only [List.length_append] using this
    have hposP : ∀ x ∈ P, 0 < x := by
      intro x hx
      rw [hPdef] at hx
      simpa using (List.mem_filter.mp hx).2
    have hcast : (P.map Int.toNat).map (fun a : ℕ => (a : ℤ)) = P := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id P]
      apply List.map_congr_left
      intro x hx
      have := hposP x hx
      simp only [Function.comp_apply, id]
      omega
    refine ⟨P.map Int.toNat, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map]; omega
    · have hPs : P.Pairwise (fun a b => b ≤ a) := hsort.filter _
      rw [List.pairwise_map]
      exact hPs.imp (fun h => Int.toNat_le_toNat h)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have := hposP x hx
      omega
    · have hneg : ((P.map Int.toNat).reverse.map fun a : ℕ => -(a : ℤ)) = N := by
        rw [hN]
        conv_rhs => rw [← hcast]
        simp [List.map_reverse, List.map_map, Function.comp_def]
      have hZ' : Z = List.replicate (n - 2 * P.length) 0 := by
        rw [hZ]
        congr 1
        omega
      rw [label_list_eq_signed, hcast, List.length_map, hneg, ← hZ']
      exact hsplit
  · rintro ⟨s, hs, hsort, hpos, rfl⟩
    rw [label_list_eq_signed]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_replicate, List.length_reverse]
      omega
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hsort.imp (fun h => by exact_mod_cast h)
      · rw [List.pairwise_replicate]
        right; exact le_refl _
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [List.eq_of_mem_replicate hb]
        exact_mod_cast Nat.zero_le x
      · rw [List.pairwise_map, List.pairwise_reverse]
        refine hsort.imp (fun h => ?_)
        simp only [neg_le_neg_iff]
        exact_mod_cast h
      · intro a ha b hb
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
        have hb0 : -(y : ℤ) ≤ 0 := by simp
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
          have : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
          omega
        · rw [List.eq_of_mem_replicate ha]
          exact hb0
    · simp [dualLab, List.map_append, List.reverse_append, List.map_reverse, List.map_map,
        Function.comp_def, List.map_replicate, List.reverse_replicate]

end GlobalTheory.Hk3
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLat
variable {D : D7}

theorem under_eq_of_delta {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : GlobalTheory.IdemSupport.Comp D Φ)
    {P : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h1 : Φ (algebraMap (AF D.host.F) (AE D) ε) P ≠ 0) : P.under (𝓞 D.host.F) = v := by
  by_contra hne
  exact h1 ((GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P hne)

theorem place_of_primeIdem {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε ∧ P.under (𝓞 D.host.F) = v := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.1 P e f h).1
  rcases h with ⟨hid, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, hT⟩
  · obtain ⟨h1, h2, v, ε, hε, hsum⟩ := hid.1
    refine ⟨v, ε, hε, hsum, under_eq_of_delta hΦ hε ?_⟩
    have hinf : infPart D e = 0 := by
      have : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
      rw [this, map_mul, hsum, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, mul_zero]
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ h1 hinf P).1 hid.2
    have hc0 : Φ (cA D e) P = 0 := by
      have := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
      rw [h2, GlobalTheory.IdemSupport.ev_zero, hd.2.1, one_mul] at this
      exact this.symm
    rw [← hsum, GlobalTheory.IdemSupport.ev_add, hd.2.1, hc0, add_zero]
    exact one_ne_zero
  · refine ⟨v, ε, hε, rfl, under_eq_of_delta hΦ hε ?_⟩
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hff (GlobalTheory.IdemSupport.place_comp hΦ hε).1 P).1 hT
    rw [hd.2.1]; exact one_ne_zero
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem two_not_mem {P : Pl D.host.E} {e : AE D} (he : GlobalTheory.IdemSupport.Comparison₂ P e) (hc : cA D e = e) (hi : e * e = e)
    (h0 : infPart D e = 0) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hi h0 P).1 he
  have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
  rw [hc] at hd'
  have hPP : GlobalTheory.IdemSupport.cP P = P := by
    by_contra hne
    have := hd.2.2 _ hne
    rw [hd'.2.1] at this
    exact one_ne_zero this
  intro h2
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap]
  have : Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.sgO D x = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [GlobalTheory.IdemSupport.cO_coe, GlobalTheory.SplitIdem.star_eq_conj]
    rfl
  rw [this, ← GlobalTheory.IdemSupport.mem_cP, hPP]

theorem unit_factor {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (M : ℕ)
    (hM : (M : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ γ ∈ intAf D.host.F, ε = pairA D.host.F 0 ((M : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hM
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (M : D.host.F) = 1 := by
        rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 hM
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  · congr 1
    rw [← mul_assoc, mul_comm _ α, mul_assoc, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) M,
      ← map_mul, mul_inv_cancel₀ hM0, map_one, mul_one]
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem intAf_mul {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) :
    x * y ∈ intAf D.host.F := fun w => by
  rw [map_mul]; exact mul_mem (hx w) (hy w)

theorem pairA_mul (x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 x * pairA D.host.F 0 y = pairA D.host.F 0 (x * y) := by
  exact Prod.ext (zero_mul _) rfl

theorem pairA_smul (a : D.host.F) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 (algebraMap D.host.F _ a * x) = a • pairA D.host.F 0 x := by
  refine Prod.ext ?_ ?_
  · exact (smul_zero a).symm
  · exact (Algebra.smul_def a x).symm



theorem lat_scale (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (NS NT c : ℕ)
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ ΛS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ ΛT)
    (γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hγ : γ ∈ intAf D.host.F) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True) :
    ∃ u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) * u i j =
        (c • u') i j := by
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) with ha₀
  let φ : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) a₀
  let ψc : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) c
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)).map ψc).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨Matrix.of fun i j => (pairA D.host.F 0 (γ * α)) ⊗ₜ[D.host.F]
        (a * ((NT : D.host.E) • t) i * ∑ k, star (((NS : D.host.E) • s) k) * S.gram k j),
      AddSubgroup.subset_closure ⟨γ * α, intAf_mul hγ hα, fun v hv => (hv trivial).elim, a, ha, _, hS s hs, _, hT t ht, rfl⟩, ?_⟩
    ext i j
    simp only [ψc, φ, DistribSMul.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Pi.smul_apply]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, pairA_mul, mul_assoc (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) γ α, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)),
      pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
    congr 1
    rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
    simp only [star_mul', star_natCast, Nat.cast_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  obtain ⟨u', hu', he⟩ := key hu
  exact ⟨u', hu', fun i j => (congrFun (congrFun he i) j).symm⟩
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat

theorem isVacAt_of_isLatVac : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) ΛS ΛT (NS NT : ℕ), IsBaseFrame S βS ΛS NS → IsBaseFrame T βT ΛT NT → ∀ P : Pl D.host.E, ((NS * NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ f₀, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ → IsVacAt ψ S T P f₀ := by
  intro D ψ S T βS βT ΛS ΛT NS NT hS hT P hP f₀ hth hvac
  refine ⟨hth, fun e f' he u hu hhalf => ?_⟩
  have hNS : (NS : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_right _ h)
  have hNT : (NT : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_left _ h)
  obtain ⟨v, ε, hε, hf, hv⟩ := place_of_primeIdem he
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 P e f' he).1
  have hunder : ∀ c : ℕ, (c : 𝓞 D.host.E) ∉ P.asIdeal → ((c * NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    intro c hc h
    rw [← hv] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · rcases P.isPrime.mem_or_mem h with h | h
      · exact hc h
      · exact hNS h
    · exact hNT h
  rcases he with ⟨hid, rfl⟩ | ⟨hfe, -, hTie⟩
  · have hfu : ∀ i j, (e + cA D e) * u i j = u i j := by
      have h1 := hid.1.1
      have h2 := hid.1.2.1
      have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
      have h4 : cA D e * e = 0 := by rw [mul_comm]; exact h2
      rcases hhalf with h | h <;> intro i j
      · have h' : e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h1, h4, add_zero]
      · have h' : cA D e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h2, h3, zero_add]
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (1 * NS * NT) (hunder 1 (by rw [Nat.cast_one]; exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)))
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 1 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = u' := by
      ext i j
      rw [← hfu i j, hf, hεγ, heq, one_smul]
    subst hue
    rcases hhalf with h | h
    · exact hvac.2 e hid.1 u hu' h
    · refine hvac.2 (cA D e) ⟨by rw [← map_mul, hid.1.1], by rw [cA_cA, mul_comm]; exact hid.1.2.1, ?_⟩ u hu' h
      obtain ⟨w, η, hη, hwη⟩ := hid.1.2.2
      exact ⟨w, η, hη, by rw [cA_cA, add_comm]; exact hwη⟩
  · have hf' : e = algebraMap (AF D.host.F) (AE D) ε := hfe.symm.trans hf
    have hc : cA D e = e := by rw [hf']; exact GlobalTheory.IdemSupport.cA_algebraMap ε
    have hi : e * e = e := hfe ▸ hff
    have h0 : infPart D e = 0 := by
      obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
      rw [hf']; exact (GlobalTheory.IdemSupport.place_comp hΦ hε).1
    have h2 := two_not_mem hTie hc hi h0
    have hfu : ∀ i j, e * u i j = u i j := by
      rcases hhalf with h | h
      · exact fun i j => h i j
      · rw [hc] at h; exact fun i j => h i j
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (2 * NS * NT) (hunder 2 h2)
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 2 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = 2 • u' := by
      ext i j
      rw [← hfu i j, hf', hεγ, heq]
    rw [hue]
    exact hvac.1 u' hu'

end GlobalTheory.VacLat
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem conv_map_idem {K : Type} [Field K] {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra K H) (hz : z * z = z)
    (σ : K →+* ℂ) (g : H) : ∑ a, σ (z.coeff a) * σ (z.coeff (a⁻¹ * g)) = σ (z.coeff g) := by
  conv_rhs => rw [← hz]

  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp [map_mul]

theorem coeff_conj_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

theorem sum_rep_idem {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) :
    (∑ g, c g • ρ g) * (∑ g, c g • ρ g) = ∑ g, c g • ρ g := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, ← map_mul]
  calc ∑ a, ∑ b, (c a * c b) • ρ (a * b) = ∑ a, ∑ g, (c a * c (a⁻¹ * g)) • ρ g := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun b => by simp
    _ = ∑ g, (∑ a, c a * c (a⁻¹ * g)) • ρ g := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_smul]
    _ = ∑ g, c g • ρ g := by simp_rw [hc]

theorem sum_rep_comm {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : H) :
    Commute (∑ h, c h • ρ h) (ρ g) := by
  unfold Commute SemiconjBy
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc]
  congr 2
  group

theorem eH_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i, eH R i * eH R i = eH R i ∧ (∀ g, Commute (eH R i) (R.gW i (sg0 D A) g)) ∧ (∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv) ∧ ∀ t y, eH R i (R.thG i t y) = R.thG i t y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hX i
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := fun g => conv_map_idem _ (idemOf_mul_self A.X hX) (sg0 D A) g
  have hcc : ∀ g h, RealDat.eC (A := A) (sg0 D A) (g * h * g⁻¹) = RealDat.eC (A := A) (sg0 D A) h := fun g h => by
    unfold RealDat.eC
    rw [coeff_conj_central _ (fun b => idemOf_central A.X hX b) g h]
  have happ : ∀ x v, (R.HW i (sg0 D A)).e (eH R i x) v = R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) := fun x v => by
    unfold eH RealDat.eWf gaL

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => congrArg _ ?_
    rw [hC.models.gW i (sg0 D A) g x]; rfl
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  have hfix : ∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv := fun x => by
    rw [RealDat.Wat, mem_goodPart]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hrange ▸ LinearMap.mem_range_self _ x
        exact this
      · rw [← happ, h]
    · rintro ⟨_, h⟩
      apply hinj
      refine MultilinearMap.ext fun v => ?_
      rw [happ, h]
  have hI : eH R i * eH R i = eH R i := sum_rep_idem _ _ hc
  refine ⟨hI, fun g => sum_rep_comm _ _ hcc g, hfix, fun t y => ?_⟩
  have hm := hC.thP.thF_mem i t y
  rw [← hrange] at hm
  obtain ⟨x0, hx0⟩ := hm
  have e1 : R.thG i t y = eH R i x0 := by
    apply hinj
    rw [hC.thP.thG i t y, ← hx0]
    refine MultilinearMap.ext fun v => ?_
    rw [happ]
    exact (postOn_apply _ _ _ _).symm
  rw [e1, ← Module.End.mul_apply, hI]

end GlobalTheory.Hk3
end
end
