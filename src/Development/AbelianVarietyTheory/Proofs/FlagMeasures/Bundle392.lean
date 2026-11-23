module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle381
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle386
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle086
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle382
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle383
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBoundProductOverPlacesLabel
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem hcExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), HcExists D F := by
  intro D F X u wt ιA h0 hW hA c
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u wt ιA hW hA (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA)
  exact ⟨Φ.symm ((F u).cls0.y c * h0⁻¹), (hΦ _ _).2 (Φ.apply_symm_apply _)⟩

end GlobalTheory.St.G
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormCong

private theorem prime_dvd_int_of_cast_eq_mul {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O}
    (hq : Irreducible q) (hqℓ : q = (ℓ : O)) {m : ℤ} {c : O} (h : (m : O) = q * c) : (ℓ : ℤ) ∣ m := by
  by_contra hnd
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).2 hnd
  apply hq.not_isUnit
  have h1 : ((a * ℓ + b * m : ℤ) : O) = 1 := by rw [hab]; simp
  push_cast at h1
  rw [h, ← hqℓ] at h1
  exact isUnit_iff_exists_inv.2 ⟨a + b * c, by linear_combination h1⟩

theorem int_sq_dvd_of_eq {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O} (hq : Irreducible q)
    (hqℓ : q = (ℓ : O)) {n : ℤ} {c : O} (h : (n : O) = q ^ 2 * c) : (ℓ : ℤ) ^ 2 ∣ n := by
  obtain ⟨m, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ (c := q * c) (by rw [h]; ring)
  push_cast at h
  rw [← hqℓ] at h
  have h2 : ((m : ℤ) : O) = q * c := by
    apply mul_left_cancel₀ hq.ne_zero
    rw [h]; ring
  obtain ⟨k, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ h2
  exact ⟨k, by ring⟩

theorem exists_place_resChar (K : Type) [Field K] [NumberField K] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Formalism.MainNotions.S.Loc.resChar p = ℓ := by
  haveI hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) _ hker
  have hmem : ((ℓ : ℤ) : 𝓞 K) ∈ Q := by
    have h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (ℓ : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((ℓ : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    exact hℓ.ne_zero (Nat.cast_eq_zero.mp h0)
  refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
  haveI := hQ
  show ringChar (𝓞 K ⧸ Q) = ℓ
  have hz : ((ℓ : ℕ) : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    simpa using hmem
  rcases (Nat.dvd_prime hℓ).1 ((ringChar.spec _ ℓ).1 hz) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem sq_dvd_at (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hN : ∀ p, (FP p).NormsOK) (i : Fin 2) :
    ((D.host.g i : ℕ) : ℤ) ^ 2 ∣ (Tn : ℤ) - T'n := by
  obtain ⟨p, hp⟩ := exists_place_resChar D.host.F (D.host.g_prime i)
  have hsome : ((D.s.atP p).split).isSome := by
    rw [D.s_split p, hp]
    fin_cases i <;> simp
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨-, -, -, -, -, hm⟩ := Z.agree p
  rcases hg : (Z.M p).split with _ | g
  · rw [hg, hsg] at hm
    exact (hm : False).elim
  rw [hg, hsg] at hm
  obtain ⟨-, hq⟩ := hm
  obtain ⟨-, -, -, -, hG⟩ := hN p
  obtain ⟨-, c, hc⟩ := hG g hg
  obtain ⟨-, -, hA, hB'⟩ := hB p
  refine int_sq_dvd_of_eq (D.host.g_prime i) g.q_irr ?_ (c := c) ?_
  · apply Subtype.ext
    rw [hq, sg.q_eq, hp]
    simp
  · apply Subtype.ext
    push_cast
    rw [← hA, ← hB']
    exact hc

end GlobalTheory.NormCong

open GlobalTheory.NormCong in
theorem GlobalTheory.NormCong.norms_congr : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).NormsOK) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] := by
  intro D Z FP u u' F F' hB hN
  have h0 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 0
  have h1 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 1
  have hcop : IsCoprime (((D.host.g 0 : ℕ) : ℤ) ^ 2) (((D.host.g 1 : ℕ) : ℤ) ^ 2) := by
    apply IsCoprime.pow
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have h := dvd_sub_comm.1 (hcop.mul_dvd h0 h1)
  rw [Nat.modEq_iff_dvd, show gS D = D.host.g 0 * D.host.g 1 from rfl]
  push_cast
  rw [mul_pow]
  exact h
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusStab

theorem finrank_Vp_k (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem inGen_of_gRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel Λ d y y' hov hgen hgr
  obtain ⟨hext, hUW, -, hmove⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨h, hh, hmv⟩ := hgr
  obtain ⟨y'', hov'', hmv''⟩ := hmove h hh Λ y hov
  have hact := fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_k D p) (hRel p)
  choose act hiff _ using hact
  have heq : ∀ p, y' p = y'' p := by
    intro p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    obtain ⟨g2, he2, hm2⟩ := hmv'' p
    obtain rfl : g1 = g2 := (hext h p).unique he1 he2
    have hg : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a1 := ((hiff p) ⟨g1, hg⟩ (y p) (y' p)).1 hm1
    have a2 := ((hiff p) ⟨g1, hg⟩ (y p) (y'' p)).1 hm2
    rw [← a1, ← a2]
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨g0, hg0, hm0⟩ := hgen.1 p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    have hg1 : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a0 := ((hiff p) ⟨g0, hg0⟩ (d p) (y p)).1 hm0
    have a1 := ((hiff p) ⟨g1, hg1⟩ (y p) (y' p)).1 hm1
    refine ⟨g1 * g0, mul_mem hg1 hg0, ((hiff p) ⟨g1 * g0, mul_mem hg1 hg0⟩ (d p) (y' p)).2 ?_⟩
    letI := act p
    let a : (FP p).UW0 := ⟨g1, hg1⟩
    let b : (FP p).UW0 := ⟨g0, hg0⟩
    have hm : (a * b) • d p = a • (b • d p) := mul_smul a b (d p)
    change (a * b) • d p = y' p
    rw [hm]
    change a • (act p).smul b (d p) = y' p
    rw [a0]
    exact a1
  · have full_of_over (L : LV D) (z : Dat Z FP) (hz : LocOver L z) :
        Submodule.IsFullLattice D.host.E L := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
      obtain ⟨t, ht, heq⟩ := hz.2 p
      have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p L : Set (Vp D p)) = ⊤ := by
        rw [← heq]
        exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (z p) t ht).2
      let U := Submodule.span D.host.E (L : Set (VS D).V)
      let b := Module.finBasis D.host.E U
      let W := Submodule.span (D.s.atP p).Ep
        (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
      have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
        have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
        change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
        rw [map_sum, map_sum] at hx
        rw [← hx]
        exact W.sum_mem fun i _ => by
          rw [map_smul, baseChange_smul₂]
          exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
      have htop : W = ⊤ := by
        apply top_le_iff.mp
        rw [← hspan, lattice₂, Submodule.span_span_of_tower]
        refine Submodule.span_le.2 ?_
        rintro y ⟨x, hx, heq⟩
        rw [← heq]
        exact hW ⟨x, Submodule.subset_span hx⟩
      refine { toIsLattice := hz.1, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
      rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
      simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
        finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
    have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D Z).1 Λ (Formalism.HermitianLatticesTheory.gmap h Λ) (full_of_over Λ y hov) (full_of_over _ y'' hov'')).1
    refine (hfin.union hgen.2).subset fun p hp => ?_
    by_cases hyd : y p = d p
    · left
      intro hl
      apply hp
      rw [heq p, ← hyd]
      obtain ⟨τ, hτ, hL⟩ := hov.2 p
      obtain ⟨τ'', hτ'', hL''⟩ := hov''.2 p
      have hlam : τ''.abelian₂ = τ.abelian₂ := by rw [hL'', hL]; exact hl.symm
      have key := GlobalTheory.T.hermitianDatum_eq_of_same_lattice (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
        (finrank_Vp_k D p) (hRel p) (y'' p) (y p) τ'' τ hτ'' hτ
      exact key hlam
    · right
      exact hyd

end GlobalTheory.GenusStab
end
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.GlueOrbit

variable {D : D7}

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hmap : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E (((LatLoc.cE D).toLinearMap) '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hmap).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

theorem img_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (L : Submodule M.L.O V) :
    LocNG.img (1 : V ≃ₗ[E] V) L = L := by
  ext x
  simp [LocNG.img]

theorem img_lattice {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  unfold LocNG.img
  rw [Submodule.map_coe]
  have e1 : (⇑((g : V →ₗ[E] V).restrictScalars M.L.O) : V → V) = ⇑(g : V →ₗ[E] V) := rfl
  rw [e1, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem glue_local_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  intro D X Y u u' F F' w _ _ Z FP _ hR Λ y y' ⟨hΛ, hτ⟩ ⟨hrel, hfin⟩
  have key : ∀ p, ∃ h ∈ (FP p).UW0, (y' p = y p → h = 1) ∧
      ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (y' p) τ ∧
        τ.abelian₂ = LocNG.img h (lattice₂ D Z.M p Λ) := by
    intro p
    obtain ⟨τ, hτ1, hτ2⟩ := hτ p
    by_cases hp : y' p = y p
    · exact ⟨1, one_mem _, fun _ => rfl, τ, hp ▸ hτ1, by rw [img_one, hτ2]⟩
    · obtain ⟨g, hg, hm⟩ := hrel p
      exact ⟨g, hg, fun h => absurd h hp, _,
        (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p) g hg
          (y p) (y' p) τ hτ1 hm).1, by rw [← hτ2]⟩
  choose h hU h1 τ hτ1 hτ2 using key
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  obtain ⟨t, ht, heq⟩ := hτ p
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    let U := Submodule.span D.host.E (Λ : Set (VS D).V)
    let b := Module.finBasis D.host.E U
    let W := Submodule.span (D.s.atP p).Ep
      (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
    have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
      have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
      change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
      rw [map_sum, map_sum] at hx
      rw [← hx]
      exact W.sum_mem fun i _ => by
        rw [map_smul, baseChange_smul₂]
        exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have htop : W = ⊤ := by
      apply top_le_iff.mp
      rw [← hspan, lattice₂, Submodule.span_span_of_tower]
      refine Submodule.span_le.2 ?_
      rintro y ⟨x, hx, heq⟩
      rw [← heq]
      exact hW ⟨x, Submodule.subset_span hx⟩
    refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
    rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
      finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
  obtain ⟨Λ', hΛ', hp⟩ := (GlobalTheory.T.hermitianLattice_local_global_principle D Z).2 Λ hfull (fun p => LocNG.img (h p) (lattice₂ D Z.M p Λ))
    (fun p => by
      obtain ⟨t, ht, heq⟩ := hτ p
      apply img_lattice
      rw [← heq]
      exact GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht)
    (hfin.subset fun p hp hc => hp (by simp only [h1 p hc, img_one]))
  exact ⟨Λ', ⟨hΛ', fun p => ⟨τ p, hτ1 p, (hτ2 p).trans (hp p).symm⟩⟩, fun p => ⟨h p, hU p, (hp p).symm⟩⟩

end GlobalTheory.Unfold.GlueOrbit
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GlueOver

theorem exists_locOver : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : Dat Z FP), (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ Λ : LV D, LocOver Λ d0 := by
  intro D Z FP d0 hT hΛ
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hΛ
  have hc : ∀ p, ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ ∧
      ((∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀) →
        τ.abelian₂ = lattice₂ D Z.M p Λ₀) := by
    intro p
    by_cases h : ∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀
    · obtain ⟨τ', h1, h2⟩ := h
      exact ⟨τ', h1, fun _ => h2⟩
    · obtain ⟨τ', h1⟩ := hT p
      exact ⟨τ', h1, fun h' => absurd h' h⟩
  choose τ hτ hτ' using hc
  haveI : Infinite (PlF D) := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.F
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset hfin.toFinset
  have hp' : ∃ t, LocNG.IsTermOver (FP p) (d0 p) t ∧ t.abelian₂ = lattice₂ D Z.M p Λ₀ := by
    by_contra h
    exact hp (hfin.mem_toFinset.mpr h)
  obtain ⟨t, ht, heq⟩ := hp'
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ₀ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ₀ := by
    let U := Submodule.span D.host.E (Λ₀ : Set (VS D).V)
    let b := Module.finBasis D.host.E U
    let W := Submodule.span (D.s.atP p).Ep
      (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
    have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
      have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
      change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
      rw [map_sum, map_sum] at hx
      rw [← hx]
      exact W.sum_mem fun i _ => by
        rw [map_smul, baseChange_smul₂]
        exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have htop : W = ⊤ := by
      apply top_le_iff.mp
      rw [← hspan, lattice₂, Submodule.span_span_of_tower]
      refine Submodule.span_le.2 ?_
      rintro y ⟨x, hx, heq⟩
      rw [← heq]
      exact hW ⟨x, Submodule.subset_span hx⟩
    refine { toIsLattice := hΛ₀, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
    rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
      finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
  obtain ⟨Λ, hΛ, heq⟩ := (GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).2 Λ₀ hfull (fun p => (τ p).abelian₂)
    (fun p => GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) (τ p) (hτ p))
    (hfin.subset (fun p hp h => hp (hτ' p h)))
  exact ⟨Λ, hΛ, fun p => ⟨τ p, hτ p, (heq p).symm⟩⟩

end GlobalTheory.Unfold.GlueOver
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localOrbitLattices_inf_frameSpan_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') := by
  first | exact @GlobalTheory.FrameSpanLat.inf_span_eq | exact GlobalTheory.FrameSpanLat.inf_span_eq | (intros; apply GlobalTheory.FrameSpanLat.inf_span_eq <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_classes_lattices_fixedFramePart_boundedScale : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  first | exact @GlobalTheory.LatClassFin.classes_fin | exact GlobalTheory.LatClassFin.classes_fin | (intros; apply GlobalTheory.LatClassFin.classes_fin <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLattices_eq_of_adaptedIsometry_innerLattices_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (v : D.what₂.Word) (B : LFlag (D.sp.Y 0) D.R.rS ((Tu D v : ℕ) : D.host.E)) (ψ₀ ψ₁ : GV D) (Λa Λb : LV D), Λa ∈ Y.what₂ v → Λb ∈ Y.what₂ v → Adapt ψ₀ (lf D (X.Fu v)) B → Adapt ψ₁ (lf D (X.Fu v)) B → Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ Λa) B = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ Λb) B → Λb = Λa ∧ ∃ n ∈ NRat (lf D (X.Fu v)), n * (ψ₁⁻¹ * ψ₀) ∈ Aut0 (lf D (X.Fu v)) Λa := by
  first | exact @GlobalTheory.Unfold.SideEq.side | exact GlobalTheory.Unfold.SideEq.side | (intros; apply GlobalTheory.Unfold.SideEq.side <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localBound_productOverPlaces_label : GlobalTheory.TypeAsm.ProdC := by
  first | exact @GlobalTheory.TypeAsm.prodC_holds | exact GlobalTheory.TypeAsm.prodC_holds | (intros; apply GlobalTheory.TypeAsm.prodC_holds <;> assumption)
end
