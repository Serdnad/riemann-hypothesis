module

public import Mathlib.Topology.Algebra.Module.Basic
public import ReciprocityTheory.GroupCohomology.Bundle002
public import ReciprocityTheory.GroupCohomology.Bundle003
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
public import ReciprocityTheory.GroupCohomology.Bundle001

@[expose] public section

section

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instCCSInv (M : TRep R G) (N : Subgroup G) :
    ContinuousConstSMul R (Representation.invariants (M.rho.comp N.subtype)) :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩

abbrev invQ (M : TRep R G) (N : Subgroup G) [N.Normal] : TRep R (G ⧸ N) where
  V := Representation.invariants (M.rho.comp N.subtype)
  rho := Representation.quotientToInvariants M.rho N
  cont := by
    have hq : Topology.IsQuotientMap (fun p : G × Representation.invariants (M.rho.comp N.subtype) =>
        ((p.1 : G ⧸ N), p.2)) :=
      (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    refine Continuous.subtype_mk ?_ _
    exact M.cont.comp ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

def invP (M : TRep R G) (N : Subgroup G) [N.Normal] : Pair (invQ M N) M where
  φ := QuotientGroup.mk' N
  u := (Representation.invariants (M.rho.comp N.subtype)).subtype
  φ_cont := continuous_quot_mk
  u_cont := continuous_subtype_val
  equiv _ _ := rfl

theorem invariants_isInvRep (M : TRep R G) (N : Subgroup G) [N.Normal] : IsInvRep M N (invQ M N) (invP M N) := by
  refine ⟨rfl, Topology.IsEmbedding.subtypeVal, fun m => ?_⟩
  constructor
  · rintro ⟨v, rfl⟩ g hg
    exact v.2 ⟨g, hg⟩
  · intro h
    exact ⟨⟨m, fun g => h g.1 g.2⟩, rfl⟩

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

abbrev e1 (a : G) : Fin 1 → G := fun _ => a

theorem oneCochain_apply_fin_one (M : TRep R G) (x : M.coch.X 1) (g : Fin 1 → G) : x.1 g = x.1 (e1 (g 0)) :=
  congrArg x.1 (funext fun i => by rw [Fin.fin_one_eq_zero i])

theorem memZ {A : Cx R} {n : ℕ} (x : A.X n) : x ∈ A.Z n ↔ A.d n x = 0 := LinearMap.mem_ker

theorem memB {A : Cx R} {n : ℕ} (x : A.X (n + 1)) : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x :=
  LinearMap.mem_range

theorem H_mk {A B : Cx R} (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl

theorem mk_eq_zero_iff {A : Cx R} {n : ℕ} (z : A.Z n) :
    (Submodule.Quotient.mk z : A.H n) = 0 ↔ z.1 ∈ A.B n := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

theorem oneDifferential_val (M : TRep R G) (x : M.coch.X 1) (a b : G) :
    (M.coch.d 1 x).1 ![a, b] = M.rho a (x.1 (e1 b)) - x.1 (e1 (a * b)) + x.1 (e1 a) := by
  show ReciprocityTheory.Gal.dn M.rho 1 x.1 ![a, b] = _
  rw [LowDeg.dn_one_apply]
  have he : ∀ c : G, (![c] : Fin 1 → G) = e1 c := fun c => funext fun i => by
    rw [Fin.fin_one_eq_zero i]; rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, he]

theorem wach_d1_eq_zero_iff (M : TRep R G) (x : M.coch.X 1) :
    M.coch.d 1 x = 0 ↔ ∀ a b, x.1 (e1 (a * b)) = x.1 (e1 a) + M.rho a (x.1 (e1 b)) := by
  constructor
  · intro h a b
    have h1 := congrArg (fun y : M.coch.X 2 => y.1 ![a, b]) h
    simp only [oneDifferential_val] at h1
    have h2 : (0 : M.coch.X 2).1 ![a, b] = 0 := rfl
    rw [h2] at h1
    rw [← sub_eq_zero, show x.1 (e1 (a * b)) - (x.1 (e1 a) + M.rho a (x.1 (e1 b))) =
      -(M.rho a (x.1 (e1 b)) - x.1 (e1 (a * b)) + x.1 (e1 a)) by abel, h1, neg_zero]
  · intro h
    apply Subtype.ext
    funext v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, oneDifferential_val, h]
    show _ = (0 : M.V)
    abel

theorem zeroDifferential_val (M : TRep R G) (y : M.coch.X 0) (a : G) :
    (M.coch.d 0 y).1 (e1 a) = M.rho a (y.1 ![]) - y.1 ![] := by
  show ReciprocityTheory.Gal.dn M.rho 0 y.1 (e1 a) = _
  rw [LowDeg.dn_zero_apply]

def const0 (M : TRep R G) (m : M.V) : M.coch.X 0 := ⟨fun _ => m, continuous_const⟩

theorem mem_oneCoboundaries_iff (M : TRep R G) (x : M.coch.X 1) :
    x ∈ M.coch.B 1 ↔ ∃ m, ∀ a, x.1 (e1 a) = M.rho a m - m := by
  rw [memB]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1 ![], fun a => zeroDifferential_val M y a⟩
  · rintro ⟨m, hm⟩
    refine ⟨const0 M m, Subtype.ext (funext fun g => ?_)⟩
    rw [oneCochain_apply_fin_one M x g, hm, oneCochain_apply_fin_one M (M.coch.d 0 (const0 M m)) g, zeroDifferential_val]
    rfl

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cocycle_one (M : TRep R G) (x : M.coch.X 1) (hx : M.coch.d 1 x = 0) : x.1 (e1 1) = 0 := by
  have h := (wach_d1_eq_zero_iff M x).mp hx 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have h2 : x.1 (e1 1) + x.1 (e1 1) - x.1 (e1 1) = 0 := by rw [← h]; abel
  simpa using h2

theorem inf_inj (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
    (hP : IsInvRep M N Q P) : Injective (P.hom.H 1) := by
  obtain ⟨hφ, hemb, hrg⟩ := hP
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hφ]; rfl
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [H_mk, mk_eq_zero_iff, mem_oneCoboundaries_iff] at hh
  obtain ⟨m, hm⟩ := hh
  have hm' : ∀ a, P.u (z.1.1 (e1 (P.φ a))) = M.rho a m - m := hm
  have hz1 := cocycle_one Q z.1 ((memZ _).1 z.2)
  have hmN : ∀ g ∈ N, M.rho g m = m := fun g hg => by
    have := hm' g
    rw [hφa, (QuotientGroup.eq_one_iff g).2 hg, hz1, map_zero] at this
    exact (sub_eq_zero.1 this.symm)
  obtain ⟨q, rfl⟩ := (hrg m).2 hmN
  rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
  refine ⟨q, fun γ => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective γ
  apply hemb.injective
  rw [← hφa, hm' a, map_sub, P.equiv]

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh

open InflationRestrictionInvariants

universe u

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh.CCA

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section HomLemmas

variable {R : Type u} [CommRing R] {A B C : Cx R}

end HomLemmas

section Retr

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem mkR_eq {a b : G} :
    Quotient.mk (QuotientGroup.rightRel U) a = Quotient.mk _ b ↔ b * a⁻¹ ∈ U :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

theorem rep_mul (x : U) (g : G) : rep U ((x : G) * g) = rep U g := by
  unfold rep
  congr 1
  rw [mkR_eq]
  simpa [mul_inv_rev] using U.inv_mem x.2

theorem retr_mul (x : U) (g : G) : retr U ((x : G) * g) = x * retr U g := by
  apply Subtype.ext
  simp only [retr, rep_mul, Subgroup.coe_mul, mul_assoc]

theorem retr_spec (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := rfl

theorem continuous_rep (hU : IsOpen (U : Set G)) : Continuous (rep U) := by
  rw [continuous_iff_continuousAt]
  intro g
  have hmem : (fun y => y * g⁻¹) ⁻¹' (U : Set G) ∈ nhds g := by
    apply (hU.preimage (continuous_mul_const g⁻¹)).mem_nhds
    simp [U.one_mem]
  apply (continuousAt_const (y := rep U g)).congr
  filter_upwards [hmem] with y hy
  have h1 : rep U ((⟨y * g⁻¹, hy⟩ : U) * g) = rep U g := rep_mul U ⟨y * g⁻¹, hy⟩ g
  simpa using h1.symm

theorem continuous_retr (hU : IsOpen (U : Set G)) : Continuous (retr U) :=
  Continuous.subtype_mk (continuous_id.mul (continuous_rep U hU).inv) _

instance finite_rightRel [U.FiniteIndex] : Finite (Quotient (QuotientGroup.rightRel U)) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm

def cosetMul (g : G) (c : Quotient (QuotientGroup.rightRel U)) : Quotient (QuotientGroup.rightRel U) :=
  Quotient.mk _ (c.out * g)

theorem cosetMul_bij (g : G) : Bijective (cosetMul U g) := by
  have key : ∀ h : G, ∀ c, cosetMul U h⁻¹ (cosetMul U h c) = c := by
    intro h c
    unfold cosetMul
    conv_rhs => rw [← Quotient.out_eq c]
    rw [mkR_eq]
    have hw : (c.out * h) * (Quotient.mk (QuotientGroup.rightRel U) (c.out * h)).out⁻¹ ∈ U :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out (c.out * h))
    simpa [mul_inv_rev, mul_assoc] using hw
  exact ⟨Function.LeftInverse.injective (key g), Function.RightInverse.surjective (fun c => by
    simpa using key g⁻¹ c)⟩

theorem out_mul (g : G) (c : Quotient (QuotientGroup.rightRel U)) :
    c.out * g = (retr U (c.out * g) : G) * (cosetMul U g c).out := by
  rw [retr_spec]
  simp [rep, cosetMul]

end Retr

section Norm

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]

def normF (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (x : Fin (n + 1) → G) : M.V :=
  ∑ᶠ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i)

theorem normF_eq [Fintype (Quotient (QuotientGroup.rightRel U))] (n : ℕ) (F : (Fin (n + 1) → G) → M.V)
    (x : Fin (n + 1) → G) :
    normF M U n F x = ∑ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i) :=
  finsum_eq_sum_of_fintype _

theorem continuous_rho (s : G) : Continuous (M.rho s) :=
  M.cont.comp (continuous_const.prodMk continuous_id)

theorem normF_mem (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (hF : F ∈ hcoch (M.resSub U) G n) :
    normF M U n F ∈ hcoch M G n := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  refine ⟨?_, fun g x => ?_⟩
  · have : normF M U n F = fun x => ∑ c : Quotient (QuotientGroup.rightRel U),
        M.rho c.out⁻¹ (F fun i => c.out * x i) := funext (normF_eq M U n F)
    rw [this]
    refine continuous_finsetSum _ fun c _ => (continuous_rho M _).comp (hF.1.comp ?_)
    exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [normF_eq, normF_eq, map_sum]
      have key : ∀ c : Quotient (QuotientGroup.rightRel U),
          M.rho c.out⁻¹ (F fun i => c.out * (g • x i)) =
          M.rho g (M.rho (cosetMul U g c).out⁻¹ (F fun i => (cosetMul U g c).out * x i)) := by
        intro c
        have e := out_mul U g c
        have h1 : (fun i => c.out * (g • x i)) =
            fun i => retr U (c.out * g) • ((cosetMul U g c).out * x i) := by
          funext i
          show c.out * (g * x i) = (retr U (c.out * g) : G) * ((cosetMul U g c).out * x i)
          rw [← mul_assoc, ← mul_assoc, ← e]
        rw [h1, hF.2]
        show M.rho c.out⁻¹ (M.rho (retr U (c.out * g) : G) _) = _
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        rw [show (retr U (c.out * g) : G) = c.out * g * ((cosetMul U g c).out)⁻¹ by
          rw [eq_mul_inv_iff_mul_eq]; exact e.symm]
        group
      simp only [key]
      exact Fintype.sum_bijective _ (cosetMul_bij U g) _ _ fun _ => rfl

theorem normF_hd (n : ℕ) (F : (Fin (n + 1) → G) → M.V) :
    normF M U (n + 1) (hd n F) = hd n (normF M U n F) := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x

  simp only [normF_eq, hd, map_sum, map_zsmul, Finset.smul_sum]
  exact Finset.sum_comm

variable {M U}

end Norm

end

end ReciprocityTheory.Coh.CCA
end

section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

theorem lowNat_holds : LowNatStatement.{u} := by
  intro R _ G _ _ _ G' _ _ _ M M' P e₀ e₁ e₂ e₀' e₁' e₂' hL hL'
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    have hw : M'.coch.d 0 (P.hom.Z 0 ⟨c, hc⟩).1 = 0 := (P.hom.Z 0 ⟨c, hc⟩).2
    have hc' : M.coch.d 0 c = 0 := hc
    change (e₀' (M'.coch.cls 0 (P.hom.Z 0 ⟨c, hc⟩).1 hw) : M'.V) =
      P.u (e₀ (M.coch.cls 0 c hc'))
    have h1 := hL'.1 (P.hom.Z 0 ⟨c, hc⟩).1 hw
    have h2 := hL.1 c hc'
    rw [h1, h2]
    show P.u (c.1 fun i => P.φ (![] i)) = P.u (c.1 ![])
    rw [show (fun i => P.φ (![] i)) = (![] : Fin 0 → G) from funext fun i => i.elim0]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.1 c hc
    have hw : M'.coch.d 1 (P.hom.Z 1 ⟨c, hc⟩).1 = 0 := (P.hom.Z 1 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.1 (P.hom.Z 1 ⟨c, hc⟩).1 hw
    change e₁' (M'.coch.cls 1 (P.hom.Z 1 ⟨c, hc⟩).1 hw) =
      P.h1 (e₁ (M.coch.cls 1 c hc))
    rw [he', he]
    unfold Pair.h1 pairH1DecompositionMap
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g] i)) = P.u (c.1 ![P.φ g])
    rw [show (fun i => P.φ (![g] i)) = ![P.φ g] from by funext i; fin_cases i; rfl]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.2 c hc
    have hw : M'.coch.d 2 (P.hom.Z 2 ⟨c, hc⟩).1 = 0 := (P.hom.Z 2 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.2 (P.hom.Z 2 ⟨c, hc⟩).1 hw
    change e₂' (M'.coch.cls 2 (P.hom.Z 2 ⟨c, hc⟩).1 hw) =
      P.h2 (e₂ (M.coch.cls 2 c hc))
    rw [he', he]
    unfold Pair.h2 compatiblePairH2
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g.1, g.2] i)) = P.u (c.1 ![P.φ g.1, P.φ g.2])
    rw [show (fun i => P.φ (![g.1, g.2] i)) = ![P.φ g.1, P.φ g.2] from by
      funext i; fin_cases i <;> rfl]

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh

open Function

universe u

theorem groupSection_holds : GroupSectionStatement.{u} := by
  intro G _ _ _ _ _ _ U hU
  obtain ⟨t, ht, htU, hc⟩ := ContinuousSections.core U hU
  let r0 : G → U := fun g => ⟨g * (t g)⁻¹, by simpa using U.inv_mem (htU g)⟩
  have hr0 : Continuous r0 := (continuous_id.mul ht.inv).subtype_mk _
  refine ⟨fun g => r0 g * (r0 1)⁻¹, hr0.mul continuous_const, mul_inv_cancel _, ?_⟩
  intro x g
  have h : t (x * g) = t g := hc _ _ (by rw [mul_inv_cancel_right]; exact x.2)
  apply Subtype.ext
  simp only [r0, Subgroup.coe_mul, Subgroup.coe_inv, h, mul_assoc]

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh

universe u

theorem low_holds : LowStatement.{u} := by
  intro R _ G _ _ _ M
  refine ⟨fun n => ⟨LowDeg.hEquiv M n, fun x hx => ⟨_, LowDeg.hEquiv_cls M n x hx⟩⟩,
    ⟨LowDeg.cohomZeroEquivContinuous M, fun x hx => LowDeg.cohomZeroEquivContinuous_cls_apply M x hx⟩,
    ⟨LowDeg.h1EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩, ⟨LowDeg.h2EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩⟩

end ReciprocityTheory.Coh
end
