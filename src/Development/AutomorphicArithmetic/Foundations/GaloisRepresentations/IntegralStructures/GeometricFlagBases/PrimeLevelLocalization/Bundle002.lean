module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop

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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p} (F : Frame S)

theorem inId_span {ι : Type} [Fintype ι] (w : Plc E) (b : ι → 𝓞 E) (y : w.adicCompletion E) (hy : InId w (Ideal.span (Set.range b)) y) :
    ∃ z : ι → w.adicCompletionIntegers E, y = ∑ j, algebraMap (𝓞 E) (w.adicCompletion E) (b j) * (z j : w.adicCompletion E) := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Ideal.map_span, ← Set.range_comp, Ideal.mem_span_range_iff_exists_fun] at hz
  obtain ⟨c, rfl⟩ := hz
  refine ⟨c, ?_⟩
  rw [AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem InId.add {w : Plc E} {𝔟 : Ideal (𝓞 E)} {y y' : w.adicCompletion E} (h : InId w 𝔟 y) (h' : InId w 𝔟 y') : InId w 𝔟 (y + y') := by
  obtain ⟨z, hz, rfl⟩ := h
  obtain ⟨z', hz', rfl⟩ := h'
  exact ⟨z + z', add_mem hz hz', rfl⟩

theorem InId.zero (w : Plc E) (𝔟 : Ideal (𝓞 E)) : InId w 𝔟 0 := ⟨0, zero_mem _, rfl⟩

theorem InId.mul {w : Plc E} {𝔟 : Ideal (𝓞 E)} {y y' : w.adicCompletion E} (h : InId w 𝔟 y) (h' : y' ∈ w.adicCompletionIntegers E) :
    InId w 𝔟 (y * y') := by
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨z * ⟨y', h'⟩, Ideal.mul_mem_right _ _ hz, rfl⟩

theorem InId.sum {ι : Type} {w : Plc E} {𝔟 : Ideal (𝓞 E)} (s : Finset ι) {y : ι → w.adicCompletion E} (h : ∀ i, InId w 𝔟 (y i)) :
    InId w 𝔟 (∑ i ∈ s, y i) :=
  Finset.sum_induction y (InId w 𝔟) (fun _ _ => InId.add) (InId.zero w 𝔟) fun i _ => h i

theorem InId.of_mem (w : Plc E) {𝔟 : Ideal (𝓞 E)} {x : 𝓞 E} (hx : x ∈ 𝔟) : InId w 𝔟 (algebraMap (𝓞 E) (w.adicCompletion E) x) :=
  ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩

theorem mem_idHat_iff (𝔟 : Ideal (𝓞 E)) (v) :
    v ∈ idHat S.D 𝔟 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i, InId w 𝔟 (F.vec w v i) := by
  constructor
  · intro hv w hw i
    induction hv using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x, hx, u, hu, rfl⟩ := hz
      rw [F.vec_mul w hw x u]
      exact (InId.of_mem w hx).mul ((F.vec_hat u).1 hu w hw i)
    | zero => rw [map_zero]; exact InId.zero w 𝔟
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact ha.add hb
    | neg a _ ha =>
      rw [map_neg]
      simpa using ha.mul (neg_mem (one_mem _))
  · intro h
    obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian 𝔟)
    have hb' : Ideal.span (Set.range b) = 𝔟 := hb
    have key : ∀ (w : Plc E) (i : Fin n), ∃ z : Fin r → w.adicCompletionIntegers E, (p : 𝓞 E) ∉ w.asIdeal →
        F.vec w v i = ∑ j, algebraMap (𝓞 E) (w.adicCompletion E) (b j) * (z j : w.adicCompletion E) := fun w i => by
      by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
      · exact ⟨0, fun h' => absurd hw h'⟩
      · obtain ⟨z, hz⟩ := inId_span w b _ (hb' ▸ h w hw i)
        exact ⟨z, fun _ => hz⟩
    choose z hz using key
    choose u hu using fun j : Fin r => F.vec_surj (fun w i => (z w i j : w.adicCompletion E)) fun w i => (z w i j).2
    have e : v = ∑ j, mulF S.D (b j) (u j) := by
      refine sub_eq_zero.1 (F.vec_inj _ fun w hw => ?_)

      rw [map_sub, map_sum, sub_eq_zero]
      funext i
      rw [hz w i hw, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [F.vec_mul w hw (b j) (u j), hu j w hw]; rfl
    rw [e]
    refine sum_mem fun j _ => AddSubgroup.subset_closure ⟨b j, hb' ▸ Ideal.subset_span ⟨j, rfl⟩, u j, (F.vec_hat _).2 fun w hw i => ?_, rfl⟩
    rw [hu j w hw]
    exact (z w i j).2

theorem basis_vec (k : Fin n) : ∃ v ∈ LaHat S.D, ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → F.vec w v = Pi.single k 1 := by
  have hi : ∀ (w : Plc E) i, (Pi.single k 1 : Fin n → w.adicCompletion E) i ∈ w.adicCompletionIntegers E := fun w i => by
    rw [Pi.single_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  obtain ⟨v, hv⟩ := F.vec_surj (fun w => Pi.single k 1) hi
  exact ⟨v, (F.vec_hat v).2 fun w hw i => by rw [hv w hw]; exact hi w i, hv⟩

theorem nsmul_integ_iff (g : GUf E n) (c : ℕ) : (∀ v ∈ LaHat S.D, c • S.L.actG (F.j g) v ∈ LaHat S.D) ↔
    ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k, (c : w.adicCompletion E) * F.cmp w g i k ∈ w.adicCompletionIntegers E := by
  constructor
  · intro h w hw i k
    obtain ⟨v, hv, e⟩ := basis_vec F k
    have := (F.vec_hat _).1 (h v hv) w hw i
    rw [map_nsmul, F.vec_act w hw, e w hw] at this
    simpa [Frame.cmp] using this
  · intro h v hv
    refine (F.vec_hat _).2 fun w hw i => ?_
    rw [map_nsmul, F.vec_act w hw]
    show c • ∑ k, F.cmp w g i k * F.vec w v k ∈ _
    rw [nsmul_eq_mul, Finset.mul_sum]
    exact sum_mem fun k _ => by rw [← mul_assoc]; exact mul_mem (h w hw i k) ((F.vec_hat v).1 hv w hw k)

theorem integ_iff (g : GUf E n) :
    Integ S.L (F.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k, F.cmp w g i k ∈ w.adicCompletionIntegers E := by
  simpa only [Integ, one_smul, Nat.cast_one, one_mul] using nsmul_integ_iff F g 1

theorem cmp_inv (w : Plc E) (g : GUf E n) : F.cmp w g⁻¹ = ((F.a w * comp w g * (F.a w)⁻¹)⁻¹).val := by
  unfold Frame.cmp
  rw [map_inv]
  congr 1
  group

end

theorem dict_holds : Dict := by
  intro E _ _ _ A n p _ S F g
  have hmul : ∀ (g h : S.G.GAf) v, S.L.actG (g * h) v = S.L.actG g (S.L.actG h v) := fun g h v => by
    rw [map_mul, Module.End.mul_apply]
  refine ⟨integ_iff F g, ?_, fun 𝔟 _ => ?_, fun c => ?_⟩
  · have h1 : F.j g ∈ S.L.KN 1 ↔ Integ S.L (F.j g) ∧ Integ S.L (F.j g⁻¹) := by
      rw [map_inv]
      refine ⟨fun h => ⟨integ_of_mem h, integ_of_mem (inv_mem h)⟩, fun h => ?_⟩
      have key : ∀ g, Integ S.L g → S.L.CongOne 1 g := fun g hg v hv => ⟨S.L.actG g v - v, sub_mem (hg v hv) hv, by simp⟩
      exact ⟨key _ h.1, key _ h.2⟩
    rw [h1, integ_iff, integ_iff]
    constructor
    · intro h w hw
      exact (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).2 ⟨h.1 w hw, cmp_inv F w g ▸ h.2 w hw⟩
    · intro h
      refine ⟨fun w hw => ((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).1 (h w hw)).1, fun w hw => ?_⟩
      rw [cmp_inv]
      exact ((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).1 (h w hw)).2
  · have hv : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ v, F.vec w (S.L.actG (F.j g) v - v) = (F.cmp w g - 1) *ᵥ F.vec w v := fun w hw v => by
      rw [map_sub, F.vec_act w hw, Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
    constructor
    · intro h w hw i k
      obtain ⟨v, hv', e⟩ := basis_vec F k
      have := (mem_idHat_iff F 𝔟 _).1 (h v hv') w hw i
      rw [hv w hw, e w hw] at this
      simpa using this
    · intro h v hv'
      refine (mem_idHat_iff F 𝔟 _).2 fun w hw i => ?_
      rw [hv w hw]
      exact InId.sum Finset.univ fun k => (h w hw i k).mul ((F.vec_hat v).1 hv' w hw k)
  · rw [← nsmul_integ_iff]
    refine forall₂_congr fun v _ => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
    · rintro ⟨v', hv', e⟩
      rwa [← map_nsmul, ← e, ← hmul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]
    · rw [map_nsmul, ← hmul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]

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
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

open UpperTheory.Gal.CertificateRingHomMap (Sim mem_Sim cj)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)

def cutU {R : Type} [Ring R] (e : R) (he : e * e = e) (hc : ∀ x, x * e = e * x) : Rˣ →* Rˣ :=
  Units.map
    { toFun := fun x => e * x + (1 - e)
      map_one' := by simp
      map_mul' := fun x y => by
        have h1 : e * x * (e * y) = e * (x * y) := by rw [mul_assoc, ← mul_assoc x, hc, mul_assoc, ← mul_assoc, he]
        have h2 : e * x * (1 - e) = 0 := by rw [← hc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero]
        have h3 : (1 - e) * (e * y) = 0 := by rw [← mul_assoc, sub_mul, one_mul, he, sub_self, zero_mul]
        have h4 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, sub_mul, one_mul, he, sub_self, sub_zero]
        rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add] }

theorem sim_cut {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (i : B →+* A) (n : ℕ) (e : B) (he : e * e = e)
    (hσ : σ (i e) = i e) : ∃ π : Sim σ i n →* Sim σ i n, ∀ g, (π g).1.1.val = i e • g.1.1.val + (1 - i e) • 1 := by
  have hie : i e * i e = i e := by rw [← map_mul, he]
  have h1 : (i e • (1 : Matrix (Fin n) (Fin n) A)) * (i e • 1) = i e • 1 := by simp [smul_smul, hie]
  have h2 : ∀ x : Matrix (Fin n) (Fin n) A, x * (i e • 1) = (i e • 1) * x := by simp
  have hv : ∀ g : GL (Fin n) A, (cutU _ h1 h2 g).val = i e • g.val + (1 - i e) • 1 := fun g => by
    show (i e • (1 : Matrix (Fin n) (Fin n) A)) * g.val + (1 - i e • 1) = _
    simp [sub_smul]
  refine ⟨(((cutU _ h1 h2).prodMap (cutU e he fun x => mul_comm _ _)).comp (Sim σ i n).subtype).codRestrict _ fun g => ?_, fun g => hv _⟩
  have hg := mem_Sim.1 g.2
  refine mem_Sim.2 ?_
  show ((cutU _ h1 h2 g.1.1).val.map σ)ᵀ * (cutU _ h1 h2 g.1.1).val = i (e * g.1.2.val + (1 - e)) • 1
  have h3 : ((i e • g.1.1.val + (1 - i e) • (1 : Matrix (Fin n) (Fin n) A)).map σ)ᵀ = i e • (g.1.1.val.map σ)ᵀ + (1 - i e) • 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hσ]
    · simp [hσ, Matrix.one_apply, hab, Ne.symm hab]
  have h4 : i e * (1 - i e) = 0 := by rw [mul_sub, mul_one, hie, sub_self]
  have h5 : (1 - i e) * (1 - i e) = 1 - i e := by rw [sub_mul, one_mul, h4, sub_zero]
  rw [hv, h3, add_mul, mul_add, mul_add]
  simp only [smul_mul_smul_comm, hg, hie, h4, h5, mul_comm (1 - i e) (i e), zero_smul, add_zero, zero_add, smul_smul, mul_one,
    map_add, map_mul, map_sub, map_one, add_smul]

theorem nat_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (q : ℕ) (u : Plc E) :
    (q : 𝓞 E) ∈ (cj u).asIdeal ↔ (q : 𝓞 E) ∈ u.asIdeal := by
  have h := (CertificateRingHomMap.ZetaNonvanishing₂.conjLoc E 0 u).2.2.1 q
  have key : ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal ↔ Valued.v ((q : ℕ) : w.adicCompletion E) < 1 := fun w => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have : (((q : ℕ) : E) : w.adicCompletion E) = (q : w.adicCompletion E) := map_natCast (algebraMap E (w.adicCompletion E)) q
    have h2 : ((q : 𝓞 E) : E) = q := map_natCast (algebraMap (𝓞 E) E) q
    rw [← this, ← h2]
  rw [key, key, h]

theorem primeProj_holds : PrimeProj := by
  intro E _ _ _ n q _
  let e : AfQ := ⟨fun v => if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0) ∈ v.adicCompletionIntegers ℚ
    split_ifs
    exacts [one_mem _, zero_mem _]⟩
  have hev : ∀ v, e v = if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0 := fun _ => rfl
  have he : e * e = e := FiniteAdeleRing.ext (R := 𝓞 ℚ) ℚ fun v => by
    show e v * e v = e v
    rw [hev]; split_ifs <;> simp
  have hp : ∀ w : Plc E, pLoc E w (finiteAdeleMap ℚ E e) = if (q : 𝓞 E) ∈ w.asIdeal then 1 else 0 := fun w => by
    show GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w (e (below ℚ w)) = _
    have : (q : 𝓞 ℚ) ∈ (below ℚ w).asIdeal ↔ (q : 𝓞 E) ∈ w.asIdeal := by
      show algebraMap (𝓞 ℚ) (𝓞 E) q ∈ w.asIdeal ↔ _
      rw [map_natCast]
    rw [hev]
    by_cases h : (q : 𝓞 E) ∈ w.asIdeal <;> simp [h, this]
  have hσ : conjFin (GlobalTheory.SplitPts.conjE E) (finiteAdeleMap ℚ E e) = finiteAdeleMap ℚ E e :=
    FiniteAdeleRing.ext (R := 𝓞 E) E fun w => by
      have hq : ∀ b : Af E, b w = pLoc E w b := fun _ => rfl
      rw [hq, hq, pLoc_conjFin, hp, hp]
      have := nat_mem_cj q w
      by_cases h : (q : 𝓞 E) ∈ w.asIdeal <;> simp [h, this]
  obtain ⟨π, hπ⟩ := sim_cut (conjFin (GlobalTheory.SplitPts.conjE E)) (finiteAdeleMap ℚ E) n e he hσ
  have hc : ∀ (g : GUf E n) (w : Plc E) a b, (comp w g).val a b = pLoc E w (g.1.1.val a b) := fun _ _ _ _ => rfl
  refine ⟨π, fun g w => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> ext a b <;> rw [hc, hπ]
  · simp [hp, h, hc]
  · by_cases hab : a = b <;> simp [hp, h, hab, Matrix.one_apply]

end UpperTheory.Gal.Int.Geo.Pl
end
end
