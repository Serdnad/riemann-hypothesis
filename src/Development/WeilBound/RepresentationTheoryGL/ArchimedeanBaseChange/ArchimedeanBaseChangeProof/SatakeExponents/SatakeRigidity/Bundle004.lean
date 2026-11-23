module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
import Mathlib.Algebra.Module.StablyFree.Basic
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle016
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.F.Rig

theorem weight_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (π : Submodule ℂ (UA E 0 → ℂ))
    (hπ : IsAutRepU π) (τ : E →+* ℂ) : ∃ lam : DomWeight 0, HasWeightAt π τ lam := by
  let lam : DomWeight 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩
  refine ⟨lam, GlobalTheory.DefU.isIrreducible_sqRep 0 lam, ?_⟩
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ.ne_bot
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ 0 lam)
  obtain ⟨c, hc⟩ : ∃ c : Module.Dual ℂ (nablaSq ℂ 0 lam), c v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  have hg : ∀ g : GL (Fin 0) ℂ, g = 1 := fun g => Units.ext (funext fun i => i.elim0)
  have hu : ∀ y : UA E 0, y = 1 := fun y => Subtype.ext (Units.ext (funext fun i => i.elim0))
  refine ⟨LinearMap.smulRight c φ, fun h => ?_, fun w => π.smul_mem _ hφ, fun x w => ?_⟩
  · have h1 := LinearMap.congr_fun h v
    rw [LinearMap.smulRight_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.elim hc hφ0
  · rw [hg (((cEmb τ).comp (embU 0 τ).subtype) x), hu (x : UA E 0), map_one, map_one]
    rfl

theorem weightEx : WeightEx := by
  intro E _ _ _ n π hπ τ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact weight_zero π hπ τ
  · exact GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ

theorem infOfWeight_reg {n : ℕ} (lam : DomWeight n) : (infOfWeight lam).Nodup ∧
    ∀ x ∈ infOfWeight lam, ∃ k : ℤ, x = k + ((n : ℂ) - 1) / 2 := by
  refine ⟨Multiset.Nodup.map (fun k k' h => ?_) Finset.univ.nodup, fun x hx => ?_⟩
  · have h2 : ((lam.w k - ((k : ℕ) : ℤ) : ℤ) : ℂ) = ((lam.w k' - ((k' : ℕ) : ℤ) : ℤ) : ℂ) := by
      push_cast
      linear_combination h
    have h3 : lam.w k - ((k : ℕ) : ℤ) = lam.w k' - ((k' : ℕ) : ℤ) := by exact_mod_cast h2
    rcases le_total k k' with hk | hk
    · have h4 := lam.anti hk
      have h5 : (k : ℕ) ≤ k' := hk
      exact Fin.ext (by omega)
    · have h4 := lam.anti hk
      have h5 : (k' : ℕ) ≤ k := hk
      exact Fin.ext (by omega)
  · obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam.w k - ((k : ℕ) : ℤ), by push_cast; ring⟩

theorem regPart : RegPart := by
  intro E _ _ _ n D hr i τ
  obtain ⟨lam, hlam⟩ := hr τ
  have hle : D.m i τ ≤ infOfWeight lam := by
    rw [← hlam, ← Finset.add_sum_erase Finset.univ (fun j => D.m j τ) (Finset.mem_univ i)]
    exact Multiset.le_add_right _ _
  obtain ⟨h1, h2⟩ := infOfWeight_reg lam
  exact ⟨D.m i τ, D.inf i τ, Multiset.nodup_of_le hle h1, fun x hx => h2 x (Multiset.subset_of_le hle hx)⟩

theorem rStrings : RStrings := by
  intro hR E _ _ _ n D hr i
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨m, hm, hnd, hx⟩ := hR E n D hr i τ
  have hRI : RegInt (D.V i) τ := ⟨m, hm, hnd, fun x hx' y hy => by
    obtain ⟨k, rfl⟩ := hx x hx'
    obtain ⟨k', rfl⟩ := hx y hy
    exact ⟨k - k', by push_cast; ring⟩⟩
  obtain ⟨a, d, P, hu, hn, he⟩ := ascSeed_holds2.1 E (D.N i) (D.pos i) (D.V i) (D.discrete i) τ hRI
  obtain ⟨h, -⟩ := he P (Setoid.refl (α := CuspSub E a) P)
  have hda : d * a = D.N i := by simpa using h
  have hpos := D.pos i
  refine ⟨a, d, P, ?_, ?_, hu, hn, he⟩
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Nat.mul_zero] at hda
      omega
    · exact ha
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hda
      omega
    · exact hd

end PositivityTheory.Rg.BcB.F.Rig

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

theorem spehExp_injective (d : ℕ) : Function.Injective (spehExp d) := fun i j h => by
  have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    unfold spehExp at h
    linarith
  exact Fin.ext (by exact_mod_cast h')

theorem strSat : StrSat := by
  intro E _ _ _ N a d V P σ hN hV hPu hPn hA hloc ν hν
  have hd : 1 ≤ d := by
    obtain ⟨hsum, -⟩ := hA
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hsum
      omega
    · exact h
  have hex : ∀ s : ℝ, ∃ χ : Formalism.L2.Host.HChar E, χ.IsAbsPow s :=
    fun s => ⟨_, GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s⟩
  choose χ0 hχ0 using hex
  classical
  let μ : ℝ → Formalism.L2.Host.HChar E := fun s =>
    if h : ∃ k, spehExp d k = s then ν h.choose else χ0 s
  have hμ : ∀ s, (μ s).IsAbsPow s := fun s => by
    by_cases h : ∃ k, spehExp d k = s
    · simp only [μ, dif_pos h]
      have := hν h.choose
      rwa [h.choose_spec] at this
    · simp only [μ, dif_neg h]
      exact hχ0 s
  have hμk : ∀ k, μ (spehExp d k) = ν k := fun k => by
    have h : ∃ k', spehExp d k' = spehExp d k := ⟨k, rfl⟩
    simp only [μ, dif_pos h]
    rw [spehExp_injective d h.choose_spec]
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV] with w hw
  have hsph := hw (σ w) (hloc w)
  obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hsph
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a P w
  have hS := PositivityTheory.Rg.Rs.ascSeed_holds2.2 E N a d V P hN hV hPu hPn hA w τ (σ w) hτ (hloc w)
  obtain ⟨B, hB, hBT⟩ := GlobalTheory.SpehPair.exists_sat_twist hd hτ hS hT μ hμ
  have hsum : ∑ k : Fin d, B k.rev = T := by
    rw [← hBT]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl
  refine ⟨fun k => B k.rev, fun k => ?_, hsph, hsum ▸ hT⟩
  have := hB k.rev
  rwa [PositivityTheory.Rg.Rs.satakeAscent.spehExp_rev, neg_neg, hμk, CG.twist_mk] at this

end PositivityTheory.Rg.BcB.F.Rig

end
end
