module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

theorem mulF_tmul (x : 𝓞 D.F) (a : AfP p) (y : D.La) :
    mulF D x (a ⊗ₜ ((1 : ℚ) ⊗ₜ y)) = a ⊗ₜ ((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O x • y)) := rfl

theorem mulF_mem (x : 𝓞 D.F) {v} (hv : v ∈ LaHat D) : mulF D x v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, y, ha, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a, _, ha, mulF_tmul x a y⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem end_ext {f g : AfP p ⊗[ℚ] VQ D →+ AfP p ⊗[ℚ] VQ D}
    (h : ∀ (a : AfP p) (r : ℚ) (y : D.La), f (a ⊗ₜ (r ⊗ₜ y)) = g (a ⊗ₜ (r ⊗ₜ y))) (v) : f v = g v := by
  induction v using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | tmul a z =>
    induction z using TensorProduct.inductionOn with
    | add b c hb hc => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hb, hc]
    | tmul r y => exact h a r y

theorem mulF_nat_mul (N : ℕ) (x : 𝓞 D.F) (v) : mulF D ((N : 𝓞 D.F) * x) v = N • mulF D x v := by
  refine end_ext (f := (mulF D ((N : 𝓞 D.F) * x)).toAddMonoidHom) (g := (N • mulF D x).toAddMonoidHom) (fun a r y => ?_) v
  show a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] (algebraMap (𝓞 D.F) D.O ((N : 𝓞 D.F) * x) • y)) = N • a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] (algebraMap (𝓞 D.F) D.O x • y))
  rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
  exact (map_nsmul ((TensorProduct.mk ℚ _ _ a).toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ D.La r).toAddMonoidHom) N _)

theorem mulF_one (v) : mulF D 1 v = v := by
  refine end_ext (f := (mulF D 1).toAddMonoidHom) (g := AddMonoidHom.id _) (fun a r y => ?_) v
  show a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] (algebraMap (𝓞 D.F) D.O 1 • y)) = a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] y)
  rw [map_one, one_smul]

theorem actG_mulF (g : G.GAf) (x : 𝓞 D.F) (v) : L.actG g (mulF D x v) = mulF D x (L.actG g v) := by
  have key : ∀ c : AfP p ⊗[ℚ] G.C, actOn L.rep (AfP p) c * mulF D x = mulF D x * actOn L.rep (AfP p) c := by
    intro c
    induction c using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add (f := _), add_mul, mul_add, ha, hb]
    | tmul a y =>
      have h := (L.rep_range (L.rep y)).1 ⟨y, rfl⟩ (algebraMap (𝓞 D.F) D.O x)
      have h2 : (L.rep y).baseChange (AfP p) * mulF D x = mulF D x * (L.rep y).baseChange (AfP p) := by
        unfold mulF
        rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h]
      have h3 : actOn L.rep (AfP p) (a ⊗ₜ y) = a • (L.rep y).baseChange (AfP p) := by
        rw [Algebra.smul_def]
        rfl
      rw [h3, smul_mul_assoc, mul_smul_comm, h2]
  exact LinearMap.congr_fun (key _) v

theorem mem_idHat_nat (N : ℕ) (z) : z ∈ idHat D (Ideal.span {(N : 𝓞 D.F)}) ↔ ∃ w ∈ LaHat D, z = N • w := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x, hx, v, hv, rfl⟩ := hz
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 hx
      exact ⟨_, mulF_mem y hv, mulF_nat_mul N y v⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, rfl⟩ := ha
      obtain ⟨u', hu', rfl⟩ := hb
      exact ⟨u + u', add_mem hu hu', by rw [smul_add]⟩
    | neg a _ ha =>
      obtain ⟨u, hu, rfl⟩ := ha
      exact ⟨-u, neg_mem hu, by rw [smul_neg]⟩
  · rintro ⟨w, hw, rfl⟩
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.F) * 1, Ideal.mem_span_singleton.2 ⟨1, rfl⟩, w, hw, ?_⟩
    rw [mulF_nat_mul, mulF_one]

theorem Integ_idHat {g : G.GAf} (hg : Integ L g) {𝔟 : Ideal (𝓞 D.F)} {z} (hz : z ∈ idHat D 𝔟) : L.actG g z ∈ idHat D 𝔟 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, hv, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨x, hx, _, hg v hv, actG_mulF L g x v⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem actG_mul (g h : G.GAf) (v) : L.actG (g * h) v = L.actG g (L.actG h v) := by
  rw [map_mul, mul_apply_eq_comp]

theorem actG_inv_act (g : G.GAf) (v) : L.actG g⁻¹ (L.actG g v) = v := by
  rw [← actG_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem actG_act_inv (g : G.GAf) (v) : L.actG g (L.actG g⁻¹ v) = v := by
  rw [← actG_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem CongId.inv {𝔟 : Ideal (𝓞 D.F)} {g : G.GAf} (hg : Integ L g⁻¹) (h : CongId L 𝔟 g) : CongId L 𝔟 g⁻¹ := fun v hv => by
  have := neg_mem (h _ (hg v hv))
  rwa [actG_act_inv, neg_sub] at this

theorem congOne_iff (N : ℕ) (g : G.GAf) : L.CongOne N g ↔ CongId L (Ideal.span {(N : 𝓞 D.F)}) g := by
  refine forall₂_congr fun v hv => ?_
  rw [mem_idHat_nat]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [sub_eq_iff_eq_add']

theorem congOne_conj {N c : ℕ} {h u : G.GAf} (hh : Integ L h) (hb : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = c • v) (hc : 0 < c)
    (hu : L.CongOne (N * c) u) : L.CongOne N (h * u * h⁻¹) := fun v hv => by
  obtain ⟨v', hv', e⟩ := hb v hv
  obtain ⟨w, hw, e'⟩ := hu v' hv'
  refine ⟨_, hh w hw, ?_⟩
  have e1 : v' = c • L.actG h⁻¹ v := by rw [← map_nsmul, ← e, actG_inv_act]
  have e2 : c • L.actG (h * u * h⁻¹) v = c • (v + N • L.actG h w) := by
    rw [actG_mul, actG_mul, ← map_nsmul, ← map_nsmul, ← e1, e', map_add (f := _), e, map_nsmul, smul_add, smul_smul, mul_comm]
  rw [← Nat.cast_smul_eq_nsmul ℚ c, ← Nat.cast_smul_eq_nsmul ℚ c] at e2
  exact smul_right_injective _ (by exact_mod_cast hc.ne') e2

end

theorem levBasic_holds : LevBasic := by
  intro p _ D G L
  refine ⟨fun 𝔟 => ⟨⟨⟨⟨{g | g ∈ L.KN 1 ∧ CongId L 𝔟 g}, ?_⟩, one_mem _, fun v _ => by simp⟩, ?_⟩, fun _ => Iff.rfl⟩,
    fun 𝔟 𝔟' K K' h h' hle g hg => ?_, fun N g => ⟨fun hg => ⟨KN_anti (one_dvd N) hg, (congOne_iff L N g).1 hg.1⟩, fun hg => ?_⟩,
    congOne_iff L, fun 𝔟 K h k hk u hu => ?_, fun N c h hh hb hc u hu => ⟨congOne_conj L hh hb hc hu.1, ?_⟩⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_⟩
    have := add_mem (ha' _ (integ_of_mem hb v hv)) (hb' v hv)
    rwa [sub_add_sub_cancel, ← actG_mul] at this
  · rintro a ⟨ha, ha'⟩
    exact ⟨inv_mem ha, CongId.inv L (integ_of_mem (inv_mem ha)) ha'⟩
  · obtain ⟨h1, h2⟩ := (h g).1 hg
    refine (h' g).2 ⟨h1, fun v hv => AddSubgroup.closure_mono ?_ (h2 v hv)⟩
    rintro z ⟨x, hx, r⟩
    exact ⟨x, hle hx, r⟩
  · exact ⟨(congOne_iff L N g).2 hg.2, (congOne_iff L N _).2 (CongId.inv L (integ_of_mem (inv_mem hg.1)) hg.2)⟩
  · obtain ⟨h1, h2⟩ := (h u).1 hu
    refine (h _).2 ⟨mul_mem (mul_mem hk h1) (inv_mem hk), fun v hv => ?_⟩
    have := Integ_idHat L (integ_of_mem hk) (h2 _ (integ_of_mem (inv_mem hk) v hv))
    rwa [map_sub, actG_act_inv, ← actG_mul, ← actG_mul] at this
  · have := congOne_conj L hh hb hc hu.2
    rwa [show h * u⁻¹ * h⁻¹ = (h * u * h⁻¹)⁻¹ by group] at this

end UpperTheory.Gal.Int.Geo.Pl
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

def Near1 {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) (e : ℕ) (g : GLw n w) : Prop :=
  ∀ i k, InId w (w.asIdeal ^ e) ((g.val - 1) i k)

def NearNbhd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Plc E) (O : Set (GLw n w)), IsOpen O → 1 ∈ O →
    ∃ e : ℕ, ∀ e', e ≤ e' → ∀ g ∈ KGL w (n := n), Near1 w e' g → g ∈ O

def StabOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Off V p → ∃ (T : Finset (Plc E)) (e : ℕ), (∀ u ∈ T, (p : 𝓞 E) ∉ u.asIdeal ∧ (u ∈ V.S ∨ F.a u ∉ KGL u (n := n))) ∧
      ∀ k' : GUf E n, F.j k' ∈ S.L.KN 1 → (∀ u ∈ T, Near1 u e (F.a u * comp u k' * (F.a u)⁻¹)) → Stab F V (F.j k')

end UpperTheory.Gal.Int.Geo.Pl
end
end

section

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

theorem UpperTheory.Gal.Int.Geo.Pl.congOf_of :
    LevBasic → TjOK → TjIdx → CongOf := by
  intro hL hT hI E _ _ _ A n p _ S F x hx N w σ J L _ g θ ϑ hD hm
  obtain ⟨-, h2, h3, -⟩ := hL p S.D S.G S.L
  obtain ⟨l1, l2, l3, l4, l5⟩ := σ.lv
  refine ⟨σ.q, σ.r, Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, σ.K₀, σ.atp,
    ⟨ordCompl[σ.q] N.1, σ.𝔞, l1, l2, l3, l4, l5, rfl⟩, σ.isLev,
    h2 _ _ _ _ (h3 N.1) σ.isLev ((Ideal.span_singleton_le_iff_mem _).2 σ.mem), σ.mem, hD, ?_⟩
  intro i hi
  obtain ⟨j, ⟨hin, hK, hH, hM⟩, hθ⟩ := hm i hi
  refine ⟨j, hK, (hT E A n p S F x hx N w σ i hin _ hH).2, ?_, ?_, ?_⟩
  · rw [hM]; exact Dvd.intro_left _ rfl
  · intro _
    exact hI E A n p S F x hx N w σ i hin _ hH
  · rw [hθ, idx, hK]
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

section

variable {E : Type} [Field E] [NumberField E] (w : Plc E)

private theorem valued_algebraMap_adicCompletionIntegers_eq_intValuation (r : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) r : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E) w r]
  exact HeightOneSpectrum.adicCompletion.valued_coe _ _ _

theorem inId_iff_le (𝔟 : Ideal (𝓞 E)) (y : w.adicCompletion E) : InId w 𝔟 y ↔ ∃ x ∈ 𝔟, Valued.v y ≤ w.intValuation x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ Submodule.span _ _ at hz
    induction hz using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨x, hx, (valued_algebraMap_adicCompletionIntegers_eq_intValuation w x).le⟩
    | zero => exact ⟨0, 𝔟.zero_mem, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x1, h1, e1⟩ := ha
      obtain ⟨x2, h2, e2⟩ := hb
      have hab : Valued.v (((a + b : w.adicCompletionIntegers E)) : w.adicCompletion E) ≤
          max (Valued.v (a : w.adicCompletion E)) (Valued.v (b : w.adicCompletion E)) :=
        Valuation.map_add Valued.v (a : w.adicCompletion E) (b : w.adicCompletion E)
      rcases le_total (w.intValuation x1) (w.intValuation x2) with h | h
      · exact ⟨x2, h2, hab.trans (max_le (e1.trans h) e2)⟩
      · exact ⟨x1, h1, hab.trans (max_le e1 (e2.trans h))⟩
    | smul c a _ ha =>
      obtain ⟨x, hx, e⟩ := ha
      refine ⟨x, hx, ?_⟩
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      have hm : Valued.v (((c • a : w.adicCompletionIntegers E)) : w.adicCompletion E) =
          Valued.v (c : w.adicCompletion E) * Valued.v (a : w.adicCompletion E) :=
        Valuation.map_mul Valued.v (c : w.adicCompletion E) (a : w.adicCompletion E)
      rw [hm]
      exact (mul_le_of_le_one_left' hc).trans e
  · rintro ⟨x, hx, hle⟩
    have hy : y ∈ w.adicCompletionIntegers E :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hle.trans (w.intValuation_le_one x))
    by_cases h0 : w.intValuation x = 0
    · rw [h0, le_zero_iff, Valuation.zero_iff] at hle
      exact ⟨0, Ideal.zero_mem _, by simp [hle]⟩
    · set a : w.adicCompletionIntegers E := algebraMap (𝓞 E) (w.adicCompletionIntegers E) x with ha_def
      have ha : Valued.v (a : w.adicCompletion E) = w.intValuation x := valued_algebraMap_adicCompletionIntegers_eq_intValuation w x
      have ha0 : (a : w.adicCompletion E) ≠ 0 := by
        intro h
        apply h0
        rw [← ha, h, map_zero]
      have hq : y / (a : w.adicCompletion E) ∈ w.adicCompletionIntegers E := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, ha]
        exact div_le_one_of_le₀ hle zero_le'
      refine ⟨⟨_, hq⟩ * a, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hx), ?_⟩
      simp only [MulMemClass.coe_mul]
      exact div_mul_cancel₀ y ha0

end

end UpperTheory.Gal.Int.Geo.Pl
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)

namespace UpperTheory.Gal.Int.Geo.Pl

def InIdUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : Plc E) (𝔟 𝔠 : Ideal (𝓞 E)), (∃ s ∈ 𝔠, s ∉ w.asIdeal) →
  ∀ y, InId w (𝔟 * 𝔠) y ↔ InId w 𝔟 y

def ProjLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (_ : Frame S) (N : Lv p) (v : Plc E) (σ : Site S N v) (q' k : ℕ), q'.Prime → q' ≠ σ.q → ∀ K₁ : Subgroup S.G.GAf,
    IsLev S.L (Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞) K₁ → ∀ u ∈ σ.K₀, ∃ x ∈ S.L.KN N.1, x⁻¹ * u ∈ K₁

end UpperTheory.Gal.Int.Geo.Pl

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.LKTrip GlobalTheory.LKDef GlobalTheory.LKMid Formalism.BasicNotions
open UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.Int.Geo.Pl

theorem vecEx_of (h0 : SeedGU) (h1 : WtAt) : VecEx := by
  intro E _ _ _ n l d hn hd x hx U hU w₀ hw₀ hT Up hUp hu
  obtain ⟨e, J, θ, χ, hJo, hJc, htf, -, -, hcusp, hφ⟩ := hT
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨W, hW⟩ := (h1 E n hn π).1
  let m : InfinitePlace E → ℕ := fun v => ∑ i, ((W v).w i).natAbs
  have hm : ∀ v i, 0 ≤ (W v).w i + m v := fun v i => by
    have : ((W v).w i).natAbs ≤ m v := Finset.single_le_sum (f := fun i => ((W v).w i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨S, Kw, Φ, κ, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h0 E n hn d x hd hx π W hW (∑ v, ((∑ i, (W v).w i) + n * m v)) Up hUp w₀ hw₀ hu
    J (χ.comp θ) hJo hJc hφ
  exact ⟨⟨π, rfl, W, hW, m, hm, _, rfl, J, χ.comp θ, hcusp, htf, S, Kw, Φ, κ, hw₀, a1, a2, a3, a4, a5, a6, a7, a8⟩⟩

theorem wtOf_of (h0 : WtCore) : WtOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V thQ hth B y hdeg hsep
  let y₀ : GL (Fin n) E × ℚˣ := y.1
  let β : GL (Fin n) E := B.β
  have hc : ∀ z : E, S.L.e.symm z = z := fun z => S.L.e.symm_apply_eq.2 (S.L_e z).symm
  have hmin : minpoly E y₀.1.val = y₀.1.val.charpoly := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Matrix.isIntegral _)) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) ?_ |>.symm
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact hdeg.ge
  let Hc : Matrix (Fin n) (Fin n) E := (A.H n).map (IsCMField.complexConj E : E →+* E)
  have hu : IsUnit Hc.det := by
    rw [show Hc.det = _ from ((IsCMField.complexConj E : E →+* E).map_det _).symm]
    exact ((map_ne_zero _).2 (A.det_ne n)).isUnit
  have hy : y₀.1.val * β.val * (Hc⁻¹ * (y₀.1.val.map (IsCMField.complexConj E : E →+* E))ᵀ * Hc) = algebraMap ℚ _ (y₀.2 : ℚ) * β.val := y.2.1
  have hrel : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * ((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val * y₀.1.val =
      ((y₀.2 : ℚ) : E) • (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val) := by
    rw [IsUnit.unit_spec]
    have e1 : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * Hc = ((y₀.2 : ℚ) : E) • (Hc * β⁻¹.val * y₀.1⁻¹.val * β.val) := by
      have h2 := congrArg (fun M => Hc * β⁻¹.val * y₀.1⁻¹.val * M) hy
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h2
      rw [← Algebra.smul_def, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul] at h2
      simp only [Matrix.mul_assoc]
      rw [Rat.cast_smul_eq_qsmul]
      exact h2
    rw [e1]
    simp only [smul_mul_assoc, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul, Matrix.mul_one]
  have hsep' : y₀.1.val.charpoly.Separable := hmin ▸ hsep
  have key := h0 E n V.W V.m V.pos y₀.1 (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit * β⁻¹) (thQ y₀).1 y₀.2
    (by rw [Units.val_mul, ← Matrix.mul_assoc]; exact hrel) hsep' (hth y₀).1
  have e2 : thQ y₀ = ((thQ y₀).1, y₀.2⁻¹) := Prod.ext rfl (hth y₀).2
  have e3 : LocalSmoothExtension.endPol S.L (minpoly E y₀.1.val) = LocalSmoothExtension.invPol y₀.1.val.charpoly := by
    unfold LocalSmoothExtension.endPol
    rw [hmin]
    refine congrArg LocalSmoothExtension.invPol (Polynomial.ext fun i => ?_)
    exact (Polynomial.coeff_map _ _).trans (hc _)
  rw [← V.jz_eq, ← e2, ← e3] at key
  exact key

theorem expOf_of (h0 : ExpCore) (h1 : AutEx) (h2 : WtAt) (h3 : EpsIff) : ExpOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V d hd hx hG
  obtain ⟨a1, a2⟩ := h0 E n d x hd hx V.W V.m V.pos
  refine ⟨a1, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h1 E τ A.τ₀
  refine ⟨σ, hσ, fun lam hl j hj => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hj
  have e : lam = V.W.at τ := (h2 E n S.facts.pos V.π).2 V.W V.hW τ lam (by rw [V.hV]; exact hl)
  subst e
  rw [V.jz_eq]
  refine a2 τ A.τ₀ σ hσ _ (fun φ => ?_) k
  have e1 : (starRingEnd ℂ) (A.τ₀ (A.ω : E)) = σ ((starRingEnd ℂ) (τ (A.ω : E))) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← IsCMField.complexEmbedding_complexConj, hσ]
  have e2 : (σ (φ (A.ω : E)) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) ↔ φ x = -τ x := by
    rw [e1, σ.injective.eq_iff]
    exact h3 E d x A.ω hd hx hG.1 hG.2 τ φ
  exact if_congr e2 rfl rfl

end UpperTheory.Gal.Int.Geo.Pl

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

theorem atPrime_of {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] (S : Setup A n p)
    {q : ℕ} (hq : q.Prime) (hp : q ≠ p) (hg : A.Good q) {r : ℤ} (hr : (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm) {w : Plc E}
    (hw : (q : 𝓞 E) ∈ w.asIdeal) (hω : A.ω - (r : 𝓞 E) ∈ w.asIdeal) : AtPrime S.D q r w.asIdeal :=
  ⟨hq, hp, hg.1.1, hr, W2.Seed.pFormPerfSt E A n q hg.2, w.isMaximal, by
    refine Ideal.span_le.2 ?_
    rintro y (rfl | rfl)
    exacts [hw, hω]⟩

theorem siteTriv_of (hS : Sides) (hL : LevBasic) : SiteTriv := by
  intro E _ _ _ A n p _ S x hx N q hq hp hg hN w hw
  obtain ⟨r, hr, hω⟩ := (hS E A x hx q hq hg.1 w hw).2.2.2.2.2.1
  have h1 : ordCompl[q] N.1 = N.1 := by
    rw [Nat.factorization_eq_zero_of_not_dvd hN]; simp
  refine ⟨⟨q, r, ⊤, S.L.KN N.1, hg, atPrime_of S hq hp hg hr hw hω, ?_, ?_, ?_⟩, rfl, rfl⟩
  · rw [h1]
    exact ⟨N.2.1, ((Nat.Prime.coprime_iff_not_dvd hq).2 hN).symm, N.2.2, top_sup_eq _, 0, le_top⟩
  · rw [h1, Ideal.mul_top]
    exact (hL p S.D S.G S.L).2.2.1 N.1
  · rw [h1, Ideal.mul_top]
    exact Ideal.mem_span_singleton_self _

end UpperTheory.Gal.Int.Geo.Pl
end
end
