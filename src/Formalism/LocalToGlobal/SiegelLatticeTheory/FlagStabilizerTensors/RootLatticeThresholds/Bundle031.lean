module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle026
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionConjugacy
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppRedW

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW

variable {D : D7} (X : HidaSetting D)

abbrev wK (kv : Σ k : Fin 2, D.nd.PlG k) : HeightOneSpectrum (𝓞 X.B.I.E) := wB X (D.naut.plGw kv.1 kv.2)

theorem card_wK (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wK X kv).asIdeal) = D.host.g kv.1 := by
  rw [card_wB, card_res_host]

theorem card_wc {I : AutInst} (w : HeightOneSpectrum (𝓞 I.E)) :
    Nat.card (𝓞 I.E ⧸ (wc I w).asIdeal) = Nat.card (𝓞 I.E ⧸ w.asIdeal) :=
  Nat.card_congr (Ideal.quotientEquiv (wc I w).asIdeal w.asIdeal (sigO I)
    (Ideal.map_comap_of_surjective _ (sigO I).surjective w.asIdeal).symm).toEquiv

theorem card_wKc (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wc X.B.I (wK X kv)).asIdeal) = D.host.g kv.1 := by
  rw [card_wc, card_wK]

theorem mem_wB (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E) :
    a ∈ (wB X w).asIdeal ↔ RingOfIntegers.mapRingEquiv X.ιE a ∈ w.asIdeal := Iff.rfl

theorem gk_mem (kv : Σ k : Fin 2, D.nd.PlG k) : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
  rw [mem_wB, map_natCast]; exact D.naut.plGw_over kv.1 kv.2

theorem gk_mem_c (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
  natCast_mem_wc X.B.I (gk_mem X kv)

theorem not_both (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ∈ P)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨a, b, hab⟩ := hcop
  have := P.add_mem (P.mul_mem_left a h0) (P.mul_mem_left b h1)
  rw [hab] at this
  exact hP ((Ideal.eq_top_iff_one _).2 this)

theorem not_both' (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) {k k' : Fin 2} (hk : k ≠ k')
    (h0 : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) (h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  fin_cases k <;> fin_cases k'
  · exact hk rfl
  · exact not_both X P hP h0 h1
  · exact not_both X P hP h1 h0
  · exact hk rfl

theorem g_eq_cast : ((X.B.g : ℕ) : 𝓞 X.B.I.E) = ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
  rw [X.g_eq]; push_cast; ring

theorem gk_of_g {P : Ideal (𝓞 X.B.I.E)} (hP : P.IsPrime) (h : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast] at h
  rcases hP.mem_or_mem h with h | h
  exacts [⟨0, h⟩, ⟨1, h⟩]

theorem g_mem_of_gk {P : Ideal (𝓞 X.B.I.E)} {k : Fin 2} (h : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast]
  fin_cases k
  · exact P.mul_mem_right _ h
  · exact P.mul_mem_left _ h

theorem over_gk (P : HeightOneSpectrum (𝓞 X.B.I.E)) (k : Fin 2) (hP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ v : D.nd.PlG k, P = wK X ⟨k, v⟩ ∨ P = wc X.B.I (wK X ⟨k, v⟩) := by
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X P).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    rw [map_natCast]; exact hP
  obtain ⟨v, hv | hv⟩ := cover X k (toH X P) hwH
  · exact ⟨v, Or.inl (by rw [← wB_toH X P, hv])⟩
  · exact ⟨v, Or.inr (by rw [← wB_toH X P, hv, wB_conjH X])⟩

theorem over_g (P : HeightOneSpectrum (𝓞 X.B.I.E)) (hP : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ kv : Σ k : Fin 2, D.nd.PlG k, P = wK X kv ∨ P = wc X.B.I (wK X kv) := by
  obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
  obtain ⟨v, hv⟩ := over_gk X P k hk
  exact ⟨⟨k, v⟩, hv⟩

theorem wB_inj {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : wB X w = wB X w') : w = w' := by
  refine HeightOneSpectrum.ext ?_
  ext a
  obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv X.ιE).surjective a
  rw [← mem_wB, ← mem_wB, h]

theorem wK_ne {kv kv' : Σ k : Fin 2, D.nd.PlG k} (h : kv ≠ kv') : wK X kv ≠ wK X kv' := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    have hv : v ≠ v' := fun hv => h (by rw [hv])
    exact hv (D.naut.plGw_inj k (wB_inj X he))
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

theorem wK_ne_wc (kv kv' : Σ k : Fin 2, D.nd.PlG k) : wK X kv ≠ wc X.B.I (wK X kv') := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    rw [show wc X.B.I (wK X ⟨k, v'⟩) = wB X (conjH (D.naut.plGw k v')) from (wB_conjH X _).symm] at he
    have he' := wB_inj X he
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    rw [← he'] at this
    exact this
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem_c X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

theorem mem_g_of_all {a : 𝓞 X.B.I.E}
    (ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal) :
    ∃ c : 𝓞 X.B.I.E, a = ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c := by
  have hk : ∀ k : Fin 2, a ∈ Ideal.span {((D.host.g k : ℕ) : 𝓞 X.B.I.E)} := by
    intro k
    refine mem_span_of_all (D.host.g_prime k) (unram X k) fun P hPm hgP => ?_
    let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
      rw [hb] at hgP
      exact (by exact_mod_cast (D.host.g_prime k).ne_zero : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ≠ 0)
        ((Submodule.mem_bot _).1 hgP)⟩
    exact ha P' (g_mem_of_gk X hgP)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hk 0)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hk 1)
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨α, β, hαβ⟩ := hcop
  refine ⟨α * v + β * u, ?_⟩
  rw [g_eq_cast]
  calc a = (α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) + β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) * a := by rw [hαβ, one_mul]
    _ = α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * (v * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) +
        β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) * (u * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E)) := by
          rw [hv, hu]; ring
    _ = _ := by ring

theorem exists_eps (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ ε : 𝓞 X.B.I.E, ε - 1 ∈ (wK X kv).asIdeal ∧
      ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 X.B.I.E)) :=
    Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 0) ∪ Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 1)
  have hS : S.Finite := (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 0)).union
    (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 1))
  have : Finite S := hS.to_subtype
  have hcop : Pairwise (Function.onFun IsCoprime fun P : S => (P.1).asIdeal) := by
    intro P Q hPQ
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (P.1).isMaximal (Q.1).isMaximal fun h => hPQ ?_
    exact Subtype.ext (HeightOneSpectrum.ext h)
  obtain ⟨ε, hε⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun P => if P.1 = wK X kv then 1 else 0
  have hmem : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ∈ S := by
    intro P hP
    obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  refine ⟨ε, ?_, fun P hP hne => ?_⟩
  · have := hε ⟨wK X kv, hmem _ (g_mem_of_gk X (gk_mem X kv))⟩
    simpa using this
  · have := hε ⟨P, hmem P hP⟩
    simp only [if_neg hne, sub_zero] at this
    exact this

theorem eps_other (kv : Σ k : Fin 2, D.nd.PlG k) {ε : 𝓞 X.B.I.E}
    (hε : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (k' : Fin 2) (hk : k' ≠ kv.1) : ε ∈ Ideal.span {((D.host.g k' : ℕ) : 𝓞 X.B.I.E)} := by
  refine mem_span_of_all (D.host.g_prime k') (unram X k') fun P hPm hgP => ?_
  let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
    rw [hb] at hgP
    exact (by exact_mod_cast (D.host.g_prime k').ne_zero : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ≠ 0)
      ((Submodule.mem_bot _).1 hgP)⟩
  refine hε P' (g_mem_of_gk X hgP) fun he => ?_
  have h0 := gk_mem X kv
  have h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by rw [← he]; exact hgP
  exact not_both' X _ (wK X kv).isPrime.ne_top hk h1 h0

end Formalism.L2.SG.Pf.KppChar
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRhoX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
  Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.AllRowsRho
  Formalism.L2.SG.AllRowsOf Formalism.MainNotions.ArithmeticCylinders

variable {D : D7} (X : HidaSetting D)

theorem exists_b (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ b : Fin D.R.r → Fin X.B.I.n → X.B.I.E, IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) b := by
  rw [← X.n_eq]
  exact exists_redBasis (I := X.B.I) (w := wB X (D.naut.plGw kv.1 kv.2)) (hp := D.host.g_prime kv.1)
    (hcard := by rw [card_wB, card_res_host])

def redBX (kv : Σ k : Fin 2, D.nd.PlG k) : RedB X.B.I D.R.r where
  w := wB X (D.naut.plGw kv.1 kv.2)
  p := D.host.g kv.1
  hp := D.host.g_prime kv.1
  hcard := by rw [card_wB, card_res_host]
  hm := X.n_eq.symm
  b := Classical.choose (exists_b X kv)
  hb := Classical.choose_spec (exists_b X kv)

def rhoX : KSub X.B.I →* G0g D.nd := MonoidHom.pi fun kv => rhoB (redBX X kv)

theorem rhoX_apply (x : KSub X.B.I) (kv : Σ k : Fin 2, D.nd.PlG k) : rhoX X x kv = rhoB (redBX X kv) x := rfl

theorem goodAt_rhoX (x : KSub X.B.I) : GoodAt X x (rhoX X x) := by
  intro kv
  exact (redMat_iff X _ _ _ _).mpr (redMat0_of (I := X.B.I) (hb := (redBX X kv).hb) (h := rhoB_spec (redBX X kv) x))

theorem redMatB_one_of {I : AutInst} {m : ℕ} (R : RedB I m) {x : I.Gf}
    (h : ∀ i, I.fmat x *ᵥ iv I (R.b i) - iv I (R.b i) ∈ Lq I R.w) :
    RedMatB I R.w R.p R.b x (1 : Matrix (Fin m) (Fin m) (ZMod R.p)) := by
  haveI : Fact (1 < R.p) := ⟨R.hp.one_lt⟩
  intro i
  have hsum : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod R.p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
      iv I (R.b j) = iv I (R.b i) := by
    rw [Finset.sum_eq_single i]
    · simp [Matrix.one_apply_eq, ZMod.val_one]
    · intro j _ hj
      simp [Matrix.one_apply_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum]
  exact h i

theorem rhoX_eq_one_iff (x : KSub X.B.I) : rhoX X x = 1 ↔ (x : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  have hRK : Formalism.L2.SG.AllRowsOf.RedKer X :=
    Formalism.L2.SG.AllRowsOf.redKer_of (X := X) (Formalism.L2.SG.AllRowsOf.redKerOne_of (X := X)
      (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0) (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))
  constructor
  · intro h
    have h1 := goodAt_rhoX X x
    rw [h] at h1
    exact (hRK x x.2).1 h1
  · intro hx
    have hK : (x : X.B.I.Gf) ∈ X.B.I.Kset := x.2
    have hG := Formalism.L2.SG.AllRowsOf.goodAt_one_of_mem_Kg (X := X) hx
    funext kv
    rw [rhoX_apply]
    apply Units.ext
    have hR0 := (redMat_iff X _ _ _ _).mp (hG kv)
    have hR1 := hR0
    simp only [Pi.one_apply, Units.val_one] at hR1
    have hA := Formalism.L2.SG.Pf.AllRowsRedKerA.stepA (I := X.B.I) (redBX X kv).hp (redBX X kv).hcard hK hR1
    have hB : RedMatB X.B.I (redBX X kv).w (redBX X kv).p (redBX X kv).b x 1 :=
      redMatB_one_of (redBX X kv) fun i => by
        have h1 := hA _ (PIW.AdelClassFin.DictLat.iv_mem X.B.I ((redBX X kv).hb.1 i))
        rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    have h2 := matB_eq (redBX X kv) hK hB
    show ((rhoB (redBX X kv) x : GL (Fin D.R.r) (ZMod (redBX X kv).p)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p)) =
      ((1 : GL (Fin D.R.r) (ZMod (redBX X kv).p)) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p))
    rw [Units.val_one]
    exact h2

theorem ES_conj (S : Set (Tup2 D)) (γ P : G0g D.nd) : (ES S).coeff (P⁻¹ * γ * P) = (ES S).coeff γ := by
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · refine Finset.prod_congr rfl fun kv _ => ?_
    exact coeff_conj_of_central (D.ntypes.eSer_central kv.1 _) (γ kv) (P kv)
  · rfl

theorem egA_rhoX (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ)
    (x : KSub X.B.I) : egA X a x = a.coeff (rhoX X x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) := by
  have h : (x : X.B.I.Gf) ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ :=
    ⟨x.2, rhoX X x, goodAt_rhoX X x⟩
  unfold egA
  rw [dite_eq_left h]
  congr 1
  have hγ := Classical.choose_spec h.2
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      (Classical.choose h.2) kv = P⁻¹ * rhoX X x kv * P := by
    intro kv
    have h1 := (redMat_iff X _ _ _ _).mp (goodAt_rhoX X x kv)
    have h2 := (redMat_iff X _ _ _ _).mp (hγ kv)
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I _ _ (redBX X kv).hp (redBX X kv).hcard D.R.r
      (redBX X kv).hm x _ _ h1 h2
  choose P hP using hP
  have e1 : Classical.choose h.2 = P⁻¹ * rhoX X x * P := by
    funext kv
    rw [hP kv]
    rfl
  rw [e1, ha]

def RhoSurj : Prop := ∀ (D : D7) (X : HidaSetting D), Function.Surjective (rhoX X)

end Formalism.L2.SG.Pf.AllRowsRhoX
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pair

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

def mvRow (L : Iof Y.TR) (r : Rw (Y.what₂ u) (Y.what₂ u') Y.TR) : Rw (Y.what₂ u) (Y.what₂ u') Y.TR :=
  (r.1, r.2.1, r.2.2 * L)

theorem row_act (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') (hs : s.lam' = q.1) :
    row Y (act Y q γ s) = mvRow (levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1))⁻¹ (row Y s) := by
  unfold row rowOf mvRow
  rw [iota_act hIR q γ s hs]
  rfl

theorem pair_core (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC) (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll)
    (hOI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (a₁ a₂ b₁ b₂ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') (ha₁ : a₁.lam' = q.1) (ha₂ : a₂.lam' = q.1)
    (hr : row Y a₁ = row Y a₂) (hr' : row Y b₁ = row Y b₂) (hγ : b₁ = act Y q γ a₁) (h2 : a₂.toTerm = b₂.toTerm) :
    Formalism.MainNotions.S.hsInner (amp Y a₁) (amp Y a₂) = Formalism.MainNotions.S.hsInner (amp Y b₁) (amp Y b₂) := by
  have h1 : row Y (act Y q γ a₁) = row Y b₂ := by rw [← hγ]; exact hr'
  have hrow : row Y (act Y q γ a₂) = row Y b₂ :=
    (row_act hIR q γ a₂ ha₂).trans ((congrArg (mvRow _) hr.symm).trans ((row_act hIR q γ a₁ ha₁).symm.trans h1))
  have hb2 : act Y q γ a₂ = b₂ := hRF u u' _ _ ((toTerm_act q γ a₂).trans h2) hrow
  have hs : ((γ.1 : Gam X u') : X.B.I.GA).1 ∈ Hinf X u' := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.1.2).2).1
  have hP : X.piU u' (((γ.1 : Gam X u') : X.B.I.GA).1)⁻¹ =
      cl (Formalism.L2.SG.Pf.SatGramActL.piUe u' (((γ.1 : Gam X u') : X.B.I.GA).1) hs).symm := by
    ext v; rfl
  rw [hγ, ← hb2, amp_act hB hAR hOI q γ a₁ ha₁, amp_act hB hAR hOI q γ a₂ ha₂, hP]
  exact (hsInner_comp_isom _ _ _).symm

theorem pairAmpConst_of (hN : ∀ w, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X w Y.hK)
    (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC) (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) : PairAmpConst Y := by
  intro u u' t₁ t₂ r r' hr hr'
  have hab : r.1.1.toTerm = r'.1.1.toTerm := r.1.2.trans r'.1.2.symm
  obtain ⟨γ, hγ⟩ := fib_gam (hN u') hab
  have hl := lam_eq_of_row hr
  exact pair_core hRF hIR hAR hB (hOI u u') _ γ r.1.1 r.2.1 r'.1.1 r'.2.1 rfl hl.2.symm hr hr' hγ
    (r.2.2.trans r'.2.2.symm)

end Pair

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end
