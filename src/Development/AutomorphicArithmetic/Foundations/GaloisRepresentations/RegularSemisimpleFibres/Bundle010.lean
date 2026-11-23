module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle253
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks

private theorem key {N M c x y : ℕ} (hc0 : 0 < c) (h : M * c = N) :
    ((x * c : ℕ) : ZMod N) = ((y * c : ℕ) : ZMod N) ↔ x ≡ y [MOD M] := by
  subst h
  rw [ZMod.natCast_eq_natCast_iff]
  exact ⟨Nat.ModEq.mul_right_cancel' hc0.ne', Nat.ModEq.mul_right' c⟩

private theorem fix_iff {N M c x : ℕ} (t : ℕ) (hc0 : 0 < c) (h : M * c = N) :
    ((t : ℕ) : ZMod N) * ((x * c : ℕ) : ZMod N) = ((x * c : ℕ) : ZMod N) ↔ x * t ≡ x [MOD M] := by
  rw [← Nat.cast_mul, show t * (x * c) = (x * t) * c by ring]
  exact key hc0 h

private theorem quot {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) :
    (q ^ m - 1) * ((q ^ f - 1) / (q ^ m - 1)) = q ^ f - 1 ∧ 0 < (q ^ f - 1) / (q ^ m - 1) := by
  have hdvd : q ^ m - 1 ∣ q ^ f - 1 := Nat.pow_sub_one_dvd_pow_sub_one q hd
  have h1 : (q ^ m - 1) * ((q ^ f - 1) / (q ^ m - 1)) = q ^ f - 1 := Nat.mul_div_cancel' hdvd
  refine ⟨h1, Nat.pos_of_ne_zero fun h0 => ?_⟩
  rw [h0, mul_zero] at h1
  have : 2 ≤ q ^ f := le_trans hq (Nat.le_self_pow hf.ne' q)
  omega

private def cl (q f m k j : ℕ) : ZMod (q ^ f - 1) :=
  ((k * q ^ j * ((q ^ f - 1) / (q ^ m - 1)) : ℕ) : ZMod (q ^ f - 1))

private theorem cl_fix {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (k j r : ℕ) :
    ((q ^ r : ℕ) : ZMod (q ^ f - 1)) * cl q f m k j = cl q f m k j ↔
      k * q ^ j * q ^ r ≡ k * q ^ j [MOD q ^ m - 1] := by
  obtain ⟨h1, h2⟩ := quot hq hf hd
  unfold cl
  exact fix_iff (q ^ r) h2 h1

private theorem cl_eq {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) {k k' j j' : ℕ}
    (h : cl q f m k j = cl q f m k' j') : k * q ^ j ≡ k' * q ^ j' [MOD q ^ m - 1] := by
  obtain ⟨h1, h2⟩ := quot hq hf hd
  unfold cl at h
  exact (key h2 h1).1 h

private theorem pow_one_mod {q m : ℕ} (hq : 2 ≤ q) : q ^ m ≡ 1 [MOD q ^ m - 1] := by
  exact Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))

private theorem not_fix {q m k : ℕ} (hq : 2 ≤ q) (hr : Reg q m k) (j r : ℕ) (h0 : 0 < r) (h1 : r < m) :
    ¬ k * q ^ j * q ^ r ≡ k * q ^ j [MOD q ^ m - 1] := by
  have := hr.not_modEq_of_lt hq (u := j) (v := j + r) (by omega) (by omega)
  rwa [pow_add, ← mul_assoc] at this

private theorem cross {q f m m' k k' j j' : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hd' : m' ∣ f)
    (hr : Reg q m' k') (hlt : m < m') : cl q f m k j ≠ cl q f m' k' j' := by
  intro h
  have hm : 0 < m := Nat.pos_of_dvd_of_pos hd hf
  have a := (cl_fix hq hf hd k j m).2 (by simpa using (pow_one_mod (m := m) hq).mul_left (k * q ^ j))
  rw [h] at a
  exact not_fix hq hr j' m hm hlt ((cl_fix hq hf hd' k' j' m).1 a)

private theorem same {q f m k k' j j' : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hj' : j' < m)
    (h : cl q f m k j = cl q f m k' j') : ∃ i, k' ≡ k * q ^ i [MOD q ^ m - 1] := by
  refine ⟨j + (m - j'), ?_⟩
  have e := (cl_eq hq hf hd h).mul_right (q ^ (m - j'))
  have e2 : k' * q ^ j' * q ^ (m - j') = k' * q ^ m := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj'.le]
  have e3 : k * q ^ j * q ^ (m - j') = k * q ^ (j + (m - j')) := by
    rw [mul_assoc, ← pow_add]
  rw [e2, e3] at e
  have e4 : k' * q ^ m ≡ k' [MOD q ^ m - 1] := by
    simpa using (pow_one_mod (m := m) hq).mul_left k'
  exact e4.symm.trans e.symm

private theorem block_nodup {q f m k : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hr : Reg q m k) :
    ((Multiset.range m).map (cl q f m k)).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range m)
  intro x hx y hy hxy
  rw [Multiset.mem_range] at hx hy
  have e := cl_eq hq hf hd hxy
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact Reg.not_modEq_of_lt hq hr hlt (by omega) e.symm
  · exact Reg.not_modEq_of_lt hq hr hlt (by omega) e

private def blk (q f : ℕ) (L : List (ℕ × ℕ)) : Multiset (ℕ × ZMod (q ^ f - 1)) :=
  (L.map fun p => (Multiset.range p.1).map fun j => ((1 : ℕ), cl q f p.1 p.2 j)).sum

private theorem map_snd_cons (q f : ℕ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    (blk q f (p :: L)).map Prod.snd =
      (Multiset.range p.1).map (cl q f p.1 p.2) + (blk q f L).map Prod.snd := by
  simp [blk, Multiset.map_map, Function.comp_def]

private theorem mem_blk {q f : ℕ} {L : List (ℕ × ℕ)} {e : ZMod (q ^ f - 1)}
    (h : e ∈ (blk q f L).map Prod.snd) : ∃ p ∈ L, ∃ j < p.1, e = cl q f p.1 p.2 j := by
  induction L with
  | nil => simp [blk] at h
  | cons p L ih =>
    rw [map_snd_cons, Multiset.mem_add] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 h
      exact ⟨p, List.mem_cons.2 (Or.inl rfl), j, Multiset.mem_range.1 hj, rfl⟩
    · obtain ⟨r, hr, j, hj, he⟩ := ih h
      exact ⟨r, List.mem_cons.2 (Or.inr hr), j, hj, he⟩

private theorem blk_nodup {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, Reg q p.1 p.2 ∧ p.1 ∣ f)
    (hP : L.Pairwise fun p r => p.1 = r.1 → ∀ i : ℕ, ¬ r.2 ≡ p.2 * q ^ i [MOD q ^ p.1 - 1]) :
    ((blk q f L).map Prod.snd).Nodup := by
  induction L with
  | nil => simp [blk]
  | cons p L ih =>
    rw [List.pairwise_cons] at hP
    have hp := hL p (List.mem_cons.2 (Or.inl rfl))
    have hL' : ∀ r ∈ L, Reg q r.1 r.2 ∧ r.1 ∣ f := fun r hr => hL r (List.mem_cons.2 (Or.inr hr))
    rw [map_snd_cons, Multiset.nodup_add]
    refine ⟨block_nodup hq hf hp.2 hp.1, ih hL' hP.2, ?_⟩
    rw [Multiset.disjoint_left]
    intro e he1 he2
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 he1
    rw [Multiset.mem_range] at hj
    obtain ⟨r, hr, j', hj', he⟩ := mem_blk he2
    have hrr := hL' r hr
    rcases lt_trichotomy p.1 r.1 with hlt | heq | hgt
    · exact cross hq hf hp.2 hrr.2 hrr.1 hlt he
    · have he' : cl q f p.1 p.2 j = cl q f p.1 r.2 j' := by
        rw [he, heq]
      obtain ⟨i, hi⟩ := same hq hf hp.2 (by omega) he'
      exact hP.1 r hr heq i hi
    · exact cross hq hf hrr.2 hp.2 hp.1 hgt he.symm

private theorem d_quot {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) :
    (q - 1) * ((q ^ f - 1) / (q - 1)) = q ^ f - 1 ∧ 0 < (q ^ f - 1) / (q - 1) := by
  simpa using quot hq hf (one_dvd f)

private theorem d_nodup {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (D : List (ℕ × ℕ))
    (hlt : ∀ p ∈ D, p.2 < q - 1) (hnd : (D.map Prod.snd).Nodup) :
    (D.map fun p => ((p.2 * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))).Nodup := by
  obtain ⟨h1, h2⟩ := d_quot hq hf
  have e : D.map (fun p => ((p.2 * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))) =
      (D.map Prod.snd).map (fun k => ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))) := by
    rw [List.map_map]
    rfl
  rw [e]
  refine List.Nodup.map_on ?_ hnd
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  have hm := (key h2 h1).1 hxy
  have ha' := hlt a ha
  have hb' := hlt b hb
  unfold Nat.ModEq at hm
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hm

private theorem d_fix {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (k : ℕ) :
    ((q ^ 1 : ℕ) : ZMod (q ^ f - 1)) * ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1)) =
      ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1)) := by
  refine (fix_iff _ (d_quot hq hf).2 (d_quot hq hf).1).2 ?_
  simpa using (pow_one_mod (m := 1) hq).mul_left k

end UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks

open UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks in
theorem UpperTheory.Gal.InertialTypesAlt.sepOf :
    SepOf := by
  intro a Q hok hap hsp
  obtain ⟨hq, -, hL⟩ := hok
  obtain ⟨hDlt, hDnd, hL2, hP⟩ := hap
  obtain ⟨f, hf, rfl, hdiv⟩ := hsp
  have hB : ((blk a.q f a.L).map Prod.snd).Nodup :=
    blk_nodup hq hf a.L (fun p hp => ⟨(hL p hp).2, hdiv p hp⟩) hP
  have hDn := d_nodup hq hf a.D hDlt hDnd
  unfold Lbl.Sep Lbl.blocks
  rw [Multiset.map_add (f := _), Multiset.nodup_add]
  refine ⟨?_, hB, ?_⟩
  · rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map]
    exact hDn
  · rw [Multiset.disjoint_left]
    intro e he1 he2
    rw [Multiset.map_coe, Multiset.mem_coe, List.map_map] at he1
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 he1
    obtain ⟨r, hr, j, hj, he⟩ := mem_blk (q := a.q) (f := f) (L := a.L) he2
    have e1 : e = ((p.2 * ((a.q ^ f - 1) / (a.q - 1)) : ℕ) : ZMod (a.q ^ f - 1)) := hpe.symm
    have hfix := d_fix hq hf p.2
    rw [← e1, he] at hfix
    have hr' := (cl_fix hq hf (hdiv r hr) r.2 j 1).1 hfix
    exact not_fix hq (hL r hr).2 j 1 one_pos (by have := hL2 r hr; omega) hr'
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.Gal.InertialTypesAlt.indMap :
    UpperTheory.Gal.TypesAndIwahori.IndSupp → UpperTheory.Gal.TypesAndIwahori.ParaFactor → IndMap := by
  intro hSupp hPara k _ _ _ _ N s d hd W Z _ _ _ _ ρ κ j hj hjκ
  set e := stdBlocks d hd with he
  let σ := (twist ρ (deltaHalf k fun a : Fin s => Fin (d a))).comp (leviProj k e)
  have hσ : ∀ (p : parab k e), leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a)) →
      ∀ w : W, σ p w = ρ (leviProj k e p) w := by
    intro p hK w
    have h3 := deltaHalf_of_mem_leviK hK
    simp only [σ, MonoidHom.comp_apply, twist, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, h3,
      Units.val_one, one_smul]
  have key : ∀ z : Z, ∀ p : parab k e, (p : GL (Fin N) k) ∈ KOne k (Fin N) → σ p (j z) = j z := by
    intro z p hp
    have hl := (hPara k e).2 p hp
    have hK : leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a)) := by
      rw [leviK, Subgroup.mem_pi]
      rw [leviKOne, Subgroup.mem_pi] at hl
      intro a ha
      exact GlobalTheory.StepData.KOne_le_KO (hl a ha)
    have h1 := (redLevi_eq_one_iff ⟨_, hK⟩).2 hl
    have h2 := hjκ ⟨_, hK⟩ z
    rw [h1, map_one] at h2
    rw [hσ p hK]
    exact h2.symm
  choose F hF1 hF0 using fun z => hSupp (GL (Fin N) k) W (parab k e) (KOne k (Fin N)) σ (j z)
    GlobalTheory.StepData.isOpen_KOne (key z)
  have uniq : ∀ (u : W) (f f' : GL (Fin N) k → W),
      (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f ((p : GL (Fin N) k) * c) = σ p u) →
      (∀ g, (¬∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c) → f g = 0) →
      (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f' ((p : GL (Fin N) k) * c) = σ p u) →
      (∀ g, (¬∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c) → f' g = 0) →
      f = f' := by
    intro u f f' h1 h0 h1' h0'
    funext g
    by_cases hg : ∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [h1 p c hc, h1' p c hc]
    · rw [h0 g hg, h0' g hg]
  have hfix : ∀ z, F z ∈ fixed (parInd e ρ) (KOne k (Fin N)) := by
    intro z
    rw [GlobalTheory.Parabolic.mem_fixed]
    intro c hc
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (F z).1.1 (g * c) = (F z).1.1 g
    by_cases hg : ∃ (p : parab k e), ∃ c' ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hg
      rw [mul_assoc, hF1 z p _ (mul_mem hc' hc), hF1 z p c' hc']
    · rw [hF0 z g hg, hF0 z (g * c)]
      rintro ⟨p, c', hc', h⟩
      exact hg ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  let Φ : Z →ₗ[ℂ] fixed (parInd e ρ) (KOne k (Fin N)) :=
    { toFun := fun z => ⟨F z, hfix z⟩
      map_add' := by
        intro z z'
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change (F (z + z')).1.1 = (F z).1.1 + (F z').1.1
        refine uniq (j (z + z')) _ _ (hF1 _) (hF0 _) ?_ ?_
        · intro p c hc
          simp only [Pi.add_apply, hF1 z p c hc, hF1 z' p c hc, map_add (f := _)]
        · intro g hg
          simp only [Pi.add_apply, hF0 z g hg, hF0 z' g hg, add_zero]
      map_smul' := by
        intro a z
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change (F (a • z)).1.1 = a • (F z).1.1
        refine uniq (j (a • z)) _ _ (hF1 _) (hF0 _) ?_ ?_
        · intro p c hc
          simp only [Pi.smul_apply, hF1 z p c hc, map_smul]
        · intro g hg
          simp only [Pi.smul_apply, hF0 z g hg, smul_zero] }
  let ev : fixed (parInd e ρ) (KOne k (Fin N)) →ₗ[ℂ] W :=
    { toFun := fun v => v.1.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ z, (F z).1.1 1 = j z := by
    intro z
    have := hF1 z 1 1 (one_mem _)
    simpa using this
  refine ⟨Φ, ev, ?_, ?_, ?_⟩
  · intro p z
    obtain ⟨g, hg⟩ := redK_surjective (k := k) (n := Fin N) (p : GL (Fin N) 𝓀[k])
    have hgP : (g : GL (Fin N) k) ∈ parahoric k e := (coe_mem_levelPre g).2 (by rw [hg]; exact p.2)
    obtain ⟨p', x, hp'KO, hpx, hxred, c, hc, hgc⟩ := (hPara k e).1 ⟨g, hgP⟩
    have hgc' : (g : GL (Fin N) k) = (p' : GL (Fin N) k) * c := hgc
    have hproj : parahoricProj k e ⟨g, hgP⟩ = leviProj 𝓀[k] e p := by
      show leviProj 𝓀[k] _ _ = _
      exact congrArg _ (Subtype.ext (by exact hg))
    have hz' : j (κ (leviProj 𝓀[k] e p) z) = ρ x (j z) := by
      rw [← hproj, ← hxred]
      exact hjκ x z
    have hσp' : σ p' (j z) = j (κ (leviProj 𝓀[k] e p) z) := by
      rw [hz', hσ p' (by rw [hpx]; exact x.2), hpx]
    have hn := KO_le_normalizer (k := k) (n := Fin N) hp'KO
    rw [← hg]
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [levelZero_apply]
    change (F _).1.1 = fun h => (F z).1.1 (h * (g : GL (Fin N) k))
    refine uniq (j (κ (leviProj 𝓀[k] e p) z)) _ _ (hF1 _) (hF0 _) ?_ ?_
    · intro q c1 hc1
      have hc2 : (p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c ∈ KOne k (Fin N) := by
        refine mul_mem ?_ hc
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) c1).1 hc1
        simpa using this
      have heq : (q : GL (Fin N) k) * c1 * (g : GL (Fin N) k) =
          ((q * p' : parab k e) : GL (Fin N) k) * ((p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c) := by
        rw [hgc', Subgroup.coe_mul]
        group
      show (F z).1.1 ((q : GL (Fin N) k) * c1 * (g : GL (Fin N) k)) = _
      rw [heq, hF1 z (q * p') _ hc2, map_mul, Module.End.mul_apply, hσp']
    · intro h hh
      show (F z).1.1 (h * (g : GL (Fin N) k)) = 0
      apply hF0
      rintro ⟨q, c2, hc2, hq⟩
      apply hh
      refine ⟨q * p'⁻¹, (p' : GL (Fin N) k) * (c2 * c⁻¹) * (p' : GL (Fin N) k)⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hn (c2 * c⁻¹)).1 (mul_mem hc2 (inv_mem hc))
      · calc h = (h * (g : GL (Fin N) k)) * (g : GL (Fin N) k)⁻¹ := by group
          _ = _ := by
            rw [hq, hgc', Subgroup.coe_mul, Subgroup.coe_inv]
            group
  · intro γ hγ z
    obtain ⟨g, rfl⟩ := redK_surjective (k := k) (n := Fin N) γ
    show ((levelZero (parInd e ρ) (redK k (Fin N) g)) (Φ z)).1.1.1 1 = 0
    rw [levelZero_apply]
    change (F z).1.1 (1 * (g : GL (Fin N) k)) = 0
    rw [one_mul]
    apply hF0 z
    rintro ⟨p, c, hc, hpc⟩
    apply hγ
    have hcKO : c⁻¹ ∈ KO k (Fin N) := inv_mem (GlobalTheory.StepData.KOne_le_KO hc)
    have hpKO : (p : GL (Fin N) k) ∈ KO k (Fin N) := by
      have : (p : GL (Fin N) k) = g * c⁻¹ := by rw [hpc, mul_inv_cancel_right]
      rw [this]
      exact mul_mem g.2 hcKO
    have hred : redK k (Fin N) ⟨p, hpKO⟩ = redK k (Fin N) g := by
      have : (⟨p, hpKO⟩ : KO k (Fin N)) = g * ⟨c⁻¹, hcKO⟩ := by
        apply Subtype.ext
        show (p : GL (Fin N) k) = g * c⁻¹
        rw [hpc, mul_inv_cancel_right]
      rw [this, map_mul, (redK_eq_one_iff ⟨c⁻¹, hcKO⟩).2 (inv_mem hc), mul_one]
    rw [← hred, mem_parab_iff]
    intro a b i i' hab
    rw [redK_eq_zero_iff]
    have := (mem_parab_iff.1 p.2) a b i i' hab
    simp [this]
  · intro z hz
    apply hj
    rw [map_zero, ← hev z]
    exact hz
end
